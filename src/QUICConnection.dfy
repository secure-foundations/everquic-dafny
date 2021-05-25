/*
QUIC Connection - the packet-level layer that exchanges messages with a remote peer.

@summary:    Packet-level communication with a remote peer.
*/
include "Options.dfy"
include "NativeTypes.dfy"
include "QEngine.dfy"
include "QUICUtils.dfy"
include "QUICTLS.dfy"
include "QUICFFI.dfy"
include "QUICStream.dfy"
include "QUICLossAndCongestion.dfy"
include "QUICFrame.dfy"
include "QUICCrypto.dfy"
include "Misc.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "PrivateDLL.dfy"

include "HandleFFIs.dfy"
include "QStream.dfy"
include "QStreamManager.dfy"
include "QLossRecovery.dfy"
include "QPacketSpace.dfy"
include "QConnection.dfy"
include "Extern.dfy"

module QUICConnection
{
import opened Options
import opened NativeTypes
import opened QEngine
import opened QUICUtils
import opened QUICTLS
import opened QUICFFI
import opened QUICStream
import opened QUICLossAndCongestion
import opened QUICFrame
import opened QUICCrypto
import opened Misc
import opened QUICDataTypes
import opened QUICConstants
import opened PrivateDLL

import opened HandleFFIs
import opened QStream
import opened QStreamManager
import opened QLossRecovery
import opened QPacketSpace
import opened QConnection
import opened Extern

const MAX_INITIAL_PACKET_HEADER_LEN :uint32 := 76;

const MAX_HAND_SHAKE_PACKET_HEADER_LEN : uint32:= 59;

const MAX_SHORT_PACKET_HEADER_LEN : uint32 := 24;

// (** Generate a new pseudo-random connection ID of length 8 for the handshake. *)
method generate_connection_id (cil:cil_t) returns (x:connection_id_fixed)
{
    var cil32 := cil as uint32;
    var cid :array<uint8> := new uint8[cil32];

    var i := 0;
    while i < cil32
    {
        cid[i] := random_byte();
        i := i + 1;
    }

    x := connection_id_raw(cid[..], cil);
}

method generate_token() returns (x :reset_token_t)
{
    var t := new byte[stateless_reset_token_length];
    var i : uint8 := 0;
    while i < 16
    {
        var r := random_byte();
        t[i] := r as uint8;
        i := i + 1;
    }

    x := t[..];
}

// (** Determine if two connection_id_fixed instances are equal or not *)
function method cid_equal (c1:connection_id_fixed, c2:connection_id_fixed) : (x :bool)
{
    c1.len == c2.len && c1.cid == c2.cid
}

method initialize_connection_fixed(hostname:seq<char>, is_client:bool)
    returns (x: connection_fixed)
{
    var monitor := monitor_init();
    var statelessResetToken := generate_token();
    var handshakeComplete := create_event_handle(0, 0);

    x := connection_fixed(
        monitor,
        is_client,
        hostname,
        statelessResetToken,
        handshakeComplete);
}

method derive_initial_keys(remote_cid: connection_id_fixed, is_client:bool) returns (initial_keys: key_pair)
    ensures initial_keys.reader != null && initial_keys.writer != null;
{
    var dst_client := new byte[32];
    var dst_server := new byte[32];

    var len := remote_cid.len as uint32;
    var id := build_buffer_from_seq(remote_cid.cid, len);

    if is_client {
        initial_secrets(dst_client, dst_server, id, len);
    } else {
        initial_secrets(dst_server, dst_client, id, len);
    }

    initial_keys := key_pair(dst_server, dst_client);
}

method initialize_connection (hostname:seq<char>, is_client:bool, scid: connection_id_fixed, dcid: connection_id_fixed)
    returns (cs: connection)
    ensures cs.Valid();
    ensures fresh(cs)
        && fresh (cs.fixedframes)
        && fresh (cs.fixedframes.buffer)
        && fresh (cs.short_header_packets)
        && fresh (cs.short_header_packets.buffer)
        && fresh (cs.lrcc_manager)
        && fresh (cs.lrcc_manager.sent_packets)
        && fresh (cs.lrcc_manager.sent_packets.Repr)
        && fresh (cs.stream_manager)
        && fresh (cs.stream_manager.quic_streams_repr)
        && fresh (cs.stream_manager.stream_lists_repr)
        && fresh (cs.stream_manager.stream_nodes_repr)
        && fresh (cs.stream_manager.segment_lists_repr)
        && fresh (cs.stream_manager.segment_nodes_repr)
        && fresh (cs.pspace_manager)
        && fresh (cs.pspace_manager.crypto_states_repr)
        && fresh (cs.pspace_manager.ack_buffers_repr)
        && fresh (cs.pspace_manager.ps_states_repr);
{
    var initial_keys := derive_initial_keys(dcid, is_client);
    var cf_state := initialize_connection_fixed(hostname, is_client);

    var local_cid := generate_connection_id(20);
    cs := new connection(cf_state, initial_keys, local_cid, scid);

    cs.mitls_state := initialize_mitls_state(cs);

    cs.lrcc_manager.loss_detection_timer := createTimer_onLossDetectionAlarm(cs);
    cs.lrcc_manager.ping_alarm := createTimer_onPingAlarm(cs);
}

method encrypt_long_header_packet(
    cs: connection,
    spec: long_header_specifics,
    ps: packet_space,
    plain_buffer: buffer_t,
    plain_buffer_len: uint32,
    packet: buffer_t,
    max_packet_len: uint32)
    returns (x: encrypt_result)

    requires buffer_valid(packet, max_packet_len);
    requires cs.Valid();
    requires plain_buffer != null && packet != null;
    requires plain_buffer_len as int <= plain_buffer.Length;

    requires !spec.BRetry? ==> spec.payload_length as int == plain_buffer_len as int + AUTH_TAG_LENGTH as int;

    // requires plain_buffer_len as int <= packet.Length;
    modifies cs.pspace_manager.crypto_states_repr;
    modifies packet;
{
    // encrypt requires this
    if plain_buffer_len < 3 { fatal("not enough length in plain buffer"); }

    var d_cid := cs.dst_connection_id;
    var s_cid := cs.src_connection_id;

    var dcid := build_buffer_from_seq(d_cid.cid, d_cid.len as uint32);
    var scid := build_buffer_from_seq(s_cid.cid, s_cid.len as uint32);

    var header := BLong(quicVersion, dcid, d_cid.len, scid, s_cid.len, spec);

    if max_packet_len as uint64 < header_len(header) as uint64 + plain_buffer_len as uint64 + AUTH_TAG_LENGTH as uint64{
        fatal("insufficient buffer size");
    }

    x := cs.pspace_manager.encrypt_packet(ps, header, plain_buffer, plain_buffer_len, packet);
}

method encode_fixed_frames(
        plain:buffer_t,
        plain_len:uint32,
        in_offset:uint32,
        frames: fixed_frame_vector,
        lrlist:loss_tracker_list)
    returns (x:Err<(uint32, bool)>)

    requires buffer_offset_valid_pre(plain, plain_len, in_offset);
    requires frames.Valid();
    requires lrlist.Valid();

    modifies plain;
    modifies lrlist, lrlist.Repr;

    ensures frames.Valid();
    ensures lrlist.Valid();
    ensures fresh(lrlist.Repr - old(lrlist.Repr));
    ensures x.Ok? ==> in_offset <= x.value.0 <= plain_len  // can be equal
{
    var offset, close := in_offset, false;
    var i, size := 0, frames.current_size;

    while i < size
        invariant buffer_offset_valid_pre(plain, plain_len, offset);
        invariant lrlist.Valid();
        invariant frames.Valid()
        invariant fresh(lrlist.Repr - old(lrlist.Repr));
        invariant in_offset <= offset;
    {
        var frame := frames.at_index(i);
        var temp := prepare_fixed_frame(plain, plain_len, offset, frame);
        if temp.Fail? { return Fail(temp.err); }
        if temp.value == plain_len { return Fail("cannot encode all fixed frames"); }
        offset := temp.value;

        var tracker := fixed_frame_tracker(frame);
        lrlist.InsertTail(tracker);

        var close_frame := is_connection_close_frame(frame);

        if close_frame {
            close := true;
        }

        i := i + 1;
    }

    return Ok((offset, close));
}

method prepare_fixed_frames(cs:connection,
        plain:buffer_t,
        plain_len:uint32,
        offset:uint32,
        lrlist:loss_tracker_list)
    returns (x: Err<uint32>)

    requires cs.Valid();
    requires buffer_offset_valid_pre(plain, plain_len, offset);
    requires lrlist.Valid();

    modifies plain;
    modifies cs`cstate;
    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    modifies lrlist, lrlist.Repr;

    ensures cs.Valid();
    ensures lrlist.Valid();
    ensures x.Ok? ==> offset <= x.value <= plain_len;  // can be equal
    ensures fresh(lrlist.Repr - old(lrlist.Repr))
{
    var frames := cs.fixedframes;
    if frames.current_size == 0 { return Ok(offset);}

    var temp := encode_fixed_frames(plain, plain_len, offset, frames, lrlist);

    if temp.Fail? { return Fail(temp.err); }
    var offset, close := temp.value.0, temp.value.1;

    if close { cs.cstate := Closed; }
    cs.fixedframes.clear();

    return Ok(offset);
}

method prepare_crypto_frame(
        cs:connection,
        ps:packet_space,
        plain:buffer_t,
        plain_len:uint32,
        payload_offset:uint32,
        lrlist:loss_tracker_list)
    returns (x:Err<(uint32, uint62)>)

    requires buffer_offset_valid_pre(plain, plain_len, payload_offset);
    requires lrlist.Valid();
    requires cs.Valid();

    modifies plain;
    modifies lrlist, lrlist.Repr;

    modifies cs.stream_manager`segment_nodes_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;

    ensures fresh(lrlist.Repr - old(lrlist.Repr))
    ensures lrlist.Valid();
    ensures cs.Valid();
    ensures x.Ok? ==> payload_offset < x.value.0 <= plain_len;
{
    var temp := cs.stream_manager.get_send_data_from_crypto_stream(ps);
    if temp.Fail? { return Fail("no ready segment"); }

    var segment := temp.value;
    var segment_offset := segment.offset;

    var payload_offset := encode_crypto_frame(segment, plain, plain_len, payload_offset, lrlist);
    x := Ok((payload_offset, segment_offset));
}

method build_initial_packet_payload(cs: connection, max_packet_len:uint32)
    returns (x: Err<(buffer<byte>, uint32, loss_tracker_list)>)
    requires cs.Valid();
    requires max_packet_len >= INITIAL_PACKET_MIN_LENGTH;

    modifies cs.stream_manager`segment_nodes_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;
    modifies cs`cstate;
    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    ensures cs.Valid();
    ensures x.Ok? ==>  x.value.0 != null
        && (x.value.0.Length >= x.value.1 as int)
        && (max_packet_len as int >= x.value.1 as int + MAX_INITIAL_PACKET_HEADER_LEN as int + AUTH_TAG_LENGTH as int)
        && x.value.2.Valid()
        && fresh(x.value.2)
        && fresh(x.value.2.Repr);
{
    if max_packet_len <= MAX_INITIAL_PACKET_HEADER_LEN + AUTH_TAG_LENGTH
        { return Fail("not enough space for initial header"); }
    var max_payload_len := max_packet_len - MAX_INITIAL_PACKET_HEADER_LEN - AUTH_TAG_LENGTH;

    // space is available for the handshake itself.
    var plain := new byte[max_payload_len];
    var lrlist := new loss_tracker_list();

    var temp := prepare_crypto_frame(cs, INITIAL_SPACE, plain, max_payload_len, 0, lrlist);
    if temp.Fail? { return Fail("failed in encoding crypto frame\n"); }
    var payload_offset, segment_offset := temp.value.0, temp.value.1;

    if (cs.cf_state.is_client && segment_offset == 0) {
        // Sending the first Initial packet, containing ClientHello.
        var packet_overhead := MAX_INITIAL_PACKET_HEADER_LEN + PN_BYTES + AUTH_TAG_LENGTH;
        if payload_offset < 1300 && (packet_overhead + payload_offset < 1300) {
            payload_offset := 1300 - packet_overhead;
        }
        print("initial packet payload offset ", payload_offset, "\n");
        assert plain.Length >= payload_offset as int;
    } else {
        if payload_offset >= max_payload_len { fatal("not enough space for fixed frames"); }
        // Either server preparing for client, or client preparing something other than the first Initial packet
        var temp := prepare_fixed_frames(cs, plain, max_payload_len, payload_offset, lrlist);
        if temp.Fail? { return Fail("cannot encode all fixed frames"); }
        payload_offset := temp.value;
    }

    x := Ok((plain, payload_offset, lrlist));
}

method build_initial_packet(cs: connection, packet:buffer_t, max_packet_len:uint32)
    returns (x: Err<(uint32, sent_packet_fixed)>)

    requires cs.Valid();
    requires buffer_valid(packet, max_packet_len);

    modifies cs.stream_manager`segment_nodes_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;
    modifies cs`cstate;
    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    modifies cs.pspace_manager.crypto_states_repr;

    modifies packet;

    ensures x.Ok? ==> (max_packet_len >= x.value.0);
    ensures cs.Valid();
{
    if max_packet_len < INITIAL_PACKET_MIN_LENGTH {
        return Fail("the initial packet must be at least 1200 bytes");
    }
    var temp := build_initial_packet_payload(cs, max_packet_len);
    if temp.Fail? { return Fail("failed to build plain text initial packet"); }
    var payload, payload_len, lrlist := temp.value.0, temp.value.1, temp.value.2;

    var token := new byte[0];

    var spec := BInitial((payload_len + AUTH_TAG_LENGTH) as uint62, ENCODED_PN_LENGTH as uint62, token, 0);

    var prepared := encrypt_long_header_packet(cs, spec, INITIAL_SPACE, payload, payload_len, packet, max_packet_len);

    var sent_bytes := prepared.written_bytes;
    if max_packet_len < sent_bytes {
        fatal("you can't write more than provided");
    }

    var sent_packet := cs.lrcc_manager.build_sent_packet(INITIAL_SPACE, prepared.packet_number, lrlist, sent_bytes);
    return Ok((sent_bytes, sent_packet));
}

// (** Prepare an Initial packet for transmission *)
method prepare_initial_packet (cs: connection, packet:buffer_t, packet_len:uint32) returns (x:Err<uint32>)
    requires cs.Valid();
    requires buffer_valid(packet, packet_len);

    modifies cs.stream_manager`segment_nodes_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;
    modifies cs`cstate;
    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    modifies cs.lrcc_manager`time_of_last_sent_ack_eliciting_packet,
        cs.lrcc_manager`bytes_in_flight;
    modifies packet;
    modifies cs.lrcc_manager.sent_packets, cs.lrcc_manager.sent_packets.Repr;
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    modifies cs.pspace_manager.crypto_states_repr;

    ensures cs.Valid();
{
    print("[DEBUG DFY] entering prepare initial\n");
    var temp := build_initial_packet(cs, packet, packet_len);
    if temp.Fail? { return Fail("failed to build protected "); }
    var sent_bytes, sent_packet:=  temp.value.0, temp.value.1;

    print("[DEBUG DFY] exiting prepare initial\n");
    return Ok(sent_bytes);
}

method {:timeLimit 120} build_handshake_packet_payload(cs: connection, max_packet_len:uint32)
    returns (x: Err<(buffer<byte>, uint32, loss_tracker_list)>)
    requires cs.Valid();
    modifies cs.pspace_manager.ps_states_repr;
    modifies cs.stream_manager`segment_nodes_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;
    ensures cs.Valid();
    ensures x.Ok? ==> x.value.0 != null
        && (x.value.0.Length >= x.value.1 as int)
        && (max_packet_len >= x.value.1)
        && (max_packet_len as int >= x.value.1 as int + MAX_HAND_SHAKE_PACKET_HEADER_LEN as int + AUTH_TAG_LENGTH as int)
        && x.value.2.Valid()
        && fresh(x.value.2)
        && fresh(x.value.2.Repr);
{
    if max_packet_len <= MAX_HAND_SHAKE_PACKET_HEADER_LEN + AUTH_TAG_LENGTH {
        return Fail("insufficient space in the buffer");
    }
    var max_payload_length := max_packet_len - MAX_HAND_SHAKE_PACKET_HEADER_LEN - AUTH_TAG_LENGTH;

    var lrlist := new loss_tracker_list();
    var payload := new byte[max_payload_length];

   // Allowable frames are CRYPTO, ACK, PADDING, CONNECTION_CLOSE and APPLICATION_CLOSE only.
    var payload_len := prepare_ack_frame(cs, HANDSHAKE_SPACE, payload, max_payload_length, 0, lrlist);

    var temp := prepare_crypto_frame(cs, HANDSHAKE_SPACE, payload, max_payload_length, 0, lrlist);
    // in this case its ok not to have crypto data
    if temp.Ok? {payload_len := temp.value.0;}

    return Ok((payload, payload_len, lrlist));
}

// (** Prepare a Handshake packet for transmission *)
method {:timeLimit 120} prepare_handshake_packet (cs: connection, packet:buffer_t, max_packet_len:uint32) returns (x:Err<uint32>)
    requires buffer_valid(packet, max_packet_len);
    requires cs.Valid();

    modifies cs.pspace_manager.ps_states_repr,
        cs.pspace_manager.crypto_states_repr;

    modifies cs.stream_manager`segment_nodes_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;
    modifies packet;
    modifies cs.lrcc_manager`time_of_last_sent_ack_eliciting_packet,
        cs.lrcc_manager`bytes_in_flight;
    modifies cs.lrcc_manager.sent_packets, cs.lrcc_manager.sent_packets.Repr;
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    ensures cs.Valid();
    ensures x.Ok? ==> max_packet_len >= x.value
{
    print("[DEBUG DFY] prepare Handshake enter\n");
    var temp := build_handshake_packet_payload(cs, max_packet_len);
    if temp.Fail? { return Fail("failed to build handshake packet payload"); }
    var payload, payload_len, lrlist := temp.value.0, temp.value.1, temp.value.2;

    var spec := BHandshake((payload_len + AUTH_TAG_LENGTH) as uint62, ENCODED_PN_LENGTH as uint62);
    var prepared := encrypt_long_header_packet(cs, spec, HANDSHAKE_SPACE, payload, payload_len, packet, max_packet_len);
    var sent_bytes := prepared.written_bytes;

    if max_packet_len < sent_bytes {
        fatal("cannot write more than provided buffer!");
    }

    var sent_packet := cs.lrcc_manager.build_sent_packet(HANDSHAKE_SPACE, prepared.packet_number, lrlist, sent_bytes);
    return Ok(sent_bytes);
}

method encrypt_short_header_packet(
    cs: connection,
    plain_buffer: buffer_t,
    plain_buffer_len: uint32,
    packet: buffer_t,
    max_packet_len: uint32)
    returns (x: encrypt_result)

    requires buffer_valid(packet, max_packet_len);
    requires cs.Valid();
    requires plain_buffer != null;
    requires plain_buffer_len as int <= plain_buffer.Length;

    modifies packet;
    modifies cs.pspace_manager.crypto_states_repr;
{
    if plain_buffer_len < 3 { fatal("not enough length in plain buffer"); }

    var dcid := build_buffer_from_seq(cs.dst_connection_id.cid, cs.dst_connection_id.len as uint32);

    var header := BShort(
        false, // Latency Spin Bit was not available in the original implementation
        true, // Key Phase Bit was set to be on
        dcid,
        cs.dst_connection_id.len,
        ENCODED_PN_LENGTH
    );

    if header_len(header) as uint64 + plain_buffer_len as uint64 + AUTH_TAG_LENGTH as uint64 > max_packet_len as uint64 {
        fatal("not enough length in packet");
    }

    x := cs.pspace_manager.encrypt_packet(APPLICATION_SPACE, header, plain_buffer, plain_buffer_len, packet);
}

method check_crypto_stream(cs: connection)
    requires cs.Valid();
{
    var crypto_stream := cs.stream_manager.get_crypto_stream(APPLICATION_SPACE);
    var more_to_send := crypto_stream.has_send_data_pending();
    if  more_to_send { fatal("Unexpected CRYPTO frame in APPLICATION_SPACE"); }
}

method prepare_stream_frame(cs: connection,
    payload: buffer<byte>,
    max_payload_len: uint32,
    payload_offset: uint32,
    lrlist: loss_tracker_list)
    returns (x: uint32)

    requires buffer_offset_valid_pre(payload, max_payload_len, payload_offset)
    requires cs.Valid();
    requires lrlist.Valid();

    modifies cs.stream_manager`total_data_sent,
            cs.stream_manager`segment_nodes_repr;
    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;
    modifies lrlist, lrlist.Repr;
    modifies payload;

    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures cs.Valid();
    ensures lrlist.Valid();
    ensures fresh(lrlist.Repr - old(lrlist.Repr));
{
    var temp := cs.stream_manager.get_send_ready_segment(max_payload_len);
    if temp.None? { return payload_offset; }
    var stream_id, segment := temp.value.0, temp.value.1;

    if 25 + segment.datalength as uint64 > UINT32_MAX as uint64 {
        fatal("this should not have happened");
    }

    if max_payload_len - payload_offset < 25 + segment.datalength {
        fatal("this should not have happened");
    }

    print("[DEBUG DFY] prepare stream segment: ");
    print_segment(segment); 
    print("\n");

    var new_offset := encode_stream_frame(stream_id, segment, payload, max_payload_len, payload_offset, lrlist);

    return new_offset;
}

method prepare_non_stream_frames(cs: connection,
    payload: buffer<byte>,
    max_payload_len:uint32,
    lrlist: loss_tracker_list)
    returns (x: Err<prepare_result>)
    requires cs.Valid();
    requires lrlist.Valid();
    requires buffer_offset_valid_pre(payload, max_payload_len, 0)

    modifies cs`cstate;
    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    modifies cs.pspace_manager.ps_states_repr;
    modifies lrlist, lrlist.Repr
    modifies payload

    ensures cs.Valid();
    ensures lrlist.Valid();
    ensures fresh(lrlist.Repr - old(lrlist.Repr))
    ensures x.Ok? ==> 0 <= x.value.offset <= max_payload_len;  // can be equal
{
    var payload_len := prepare_ack_frame(cs, APPLICATION_SPACE, payload, max_payload_len, 0, lrlist);
    if payload_len == max_payload_len { fatal("not enough space for anything else"); }

    var temp0 := prepare_fixed_frames(cs, payload, max_payload_len, payload_len, lrlist);
    if temp0.Fail? { return Fail("cannot encode all fixed frames"); }
    payload_len := temp0.value;

    return Ok(prepare_result(payload_len, true));
}

method build_short_header_packet(cs: connection, max_packet_len:uint32)
    returns (x: Err<(buffer<byte>, uint32, loss_tracker_list)>)
    requires cs.Valid();

    modifies cs`cstate;
    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    modifies cs.pspace_manager.ps_states_repr;
    modifies cs.stream_manager`total_data_sent;

    modifies cs.stream_manager`segment_nodes_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;

    ensures cs.Valid();
    ensures x.Ok? ==>
        && x.value.0 != null
        && (x.value.0.Length >= x.value.1 as int)
        && (max_packet_len as int >= x.value.1 as int + MAX_SHORT_PACKET_HEADER_LEN as int + AUTH_TAG_LENGTH as int)
        && x.value.2.Valid()
        && fresh(x.value.2)
        && fresh(x.value.2.Repr);
{
    check_crypto_stream(cs);
    if max_packet_len <= MAX_SHORT_PACKET_HEADER_LEN + AUTH_TAG_LENGTH {
        fatal("insufficient space for payload for short header packet");
    }
    var max_payload_len := max_packet_len - MAX_SHORT_PACKET_HEADER_LEN - AUTH_TAG_LENGTH;

    var lrlist := new loss_tracker_list();
    var payload := new byte[max_payload_len];

    var temp := prepare_non_stream_frames(cs, payload, max_payload_len, lrlist);
    if temp.Fail? { return Fail("non_data frame failed"); }
    var payload_offset := temp.value.offset;

    if payload_offset >= max_payload_len {
        return Ok((payload, payload_offset, lrlist));
    }

    payload_offset := prepare_stream_frame(cs, payload, max_payload_len, payload_offset, lrlist);

    if payload_offset >= max_payload_len {
        fatal("payload_len makes no sense");
    }
    return Ok((payload, payload_offset, lrlist));
}

// (** Prepare a protected packet for transmission *)
method {:timeLimit 120} prepare_short_header_packet (cs: connection, packet:buffer_t, max_packet_len:uint32) returns (x:Err<uint32>)
    requires cs.Valid();
    requires buffer_valid(packet, max_packet_len);
    modifies cs`cstate;
    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    modifies cs.pspace_manager.ps_states_repr,
        cs.pspace_manager.crypto_states_repr;

    modifies cs.stream_manager`total_data_sent;

    modifies cs.stream_manager`segment_nodes_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;
    modifies packet;
    modifies cs.lrcc_manager.sent_packets, cs.lrcc_manager.sent_packets.Repr;
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
    modifies cs.lrcc_manager`time_of_last_sent_ack_eliciting_packet,
        cs.lrcc_manager`bytes_in_flight;

    ensures cs.Valid();
{
    var temp := build_short_header_packet(cs, max_packet_len);
    if temp.Fail? { return Fail("failed to build short header packet"); }
    var payload, payload_len, lrlist := temp.value.0, temp.value.1, temp.value.2;

    var prepared := encrypt_short_header_packet(cs, payload, payload_len, packet, max_packet_len);
    var sent_bytes := prepared.written_bytes;
    
    var sent_packet := cs.lrcc_manager.build_sent_packet(APPLICATION_SPACE, prepared.packet_number, lrlist, sent_bytes);

    cs.lrcc_manager.onPacketSent(sent_packet, sent_bytes);
    return Ok(sent_bytes);
}

method connnection_prepare_packet_impl(cs: connection, packet:buffer_t, packet_len:uint32)
    returns (x : Err<uint32>)

    requires cs.Valid();

    requires buffer_valid(packet, packet_len);

    modifies cs`cstate;
    modifies cs`ready;

    modifies cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`total_data_sent;

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;

    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    modifies cs.lrcc_manager`time_of_last_sent_ack_eliciting_packet,
        cs.lrcc_manager`bytes_in_flight;

    modifies cs.lrcc_manager.sent_packets, cs.lrcc_manager.sent_packets.Repr;
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    modifies cs.pspace_manager.ps_states_repr,
        cs.pspace_manager.crypto_states_repr;

    modifies packet;

    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));

    ensures cs.Valid();
{
    var temp := cs.connection_send_data_pending();
    if temp.None? {
        print("[WARN DFY] No data send pending\n");
        return Ok(0);
    }
    var ps := temp.value;

    print("[DEBUG DFY] connection has something to send ", ps_str(ps), "\n");

    match ps {
        case INITIAL_SPACE => {x := prepare_initial_packet(cs, packet, packet_len);}
        case HANDSHAKE_SPACE => {x := prepare_handshake_packet(cs, packet, packet_len);}
        case APPLICATION_SPACE => {x := prepare_short_header_packet(cs, packet, packet_len);}
    }

    cs.update_send_data_ready();
}

method connnection_prepare_packet(cs: connection, packet:buffer_t, packet_len:uint32)
    returns (x : Err<uint32>)

    requires cs.Valid();

    requires buffer_valid(packet, packet_len);

    modifies cs`cstate;
    modifies cs`ready;

    modifies cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`total_data_sent;

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;

    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    modifies cs.lrcc_manager`time_of_last_sent_ack_eliciting_packet,
        cs.lrcc_manager`bytes_in_flight;

    modifies cs.lrcc_manager.sent_packets, cs.lrcc_manager.sent_packets.Repr;
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    modifies cs.pspace_manager.ps_states_repr,
        cs.pspace_manager.crypto_states_repr;

    modifies packet;

    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));

    ensures cs.Valid();
{
    cs.enter_monitor();
    x := connnection_prepare_packet_impl(cs, packet, packet_len);
    cs.exit_monitor();
}

method append_connection_id (packet:buffer_t, packet_len: uint32, p:uint32, cid:connection_id_fixed)
    returns (x : uint32)
    requires buffer_offset_valid_pre(packet, packet_len, p);
    requires cid.len as int + 1 < packet_len as int - p as int;

    modifies packet;
    ensures x == p + cid.len as uint32 + 1;
{
    x := append8(packet, p, cid.len);

    if cid.len != 0 {
        x := append_sequence(packet, x, cid.cid, cid.len as uint32);
    }
}

method prepareNegotiationPacket (packet:buffer_t, packet_len:uint32, cid:connection_id_fixed) returns (x :Err<uint32>)
    requires buffer_valid(packet, packet_len);
    modifies packet;
{
    if packet_len < 100 { return Fail("insufficient space"); }

    print("[DEBUG DFY] prepareNegotiationpacket\n");
    var p := append8 (packet, 0, LONG_HEADER_MASK); // top bit must be 1, other bits are selected randomly by the server
    p := append32 (packet, p, 0); // append Version hard-coded to 0

    p := append_connection_id(packet, packet_len, p, cid); // Copy; the source cid as destination
    p := append_connection_id(packet, packet_len, p, cid); // Copy; the source cid as source also

    p := append32(packet, p, 0x0a0a0a7a); // append a test version value
    p := append32(packet, p, quicVersion); // append our supported version
    return Ok(p);
}

method parse_connection_id(packet: buffer_t, packet_len: uint32, parse_offset: uint32, cid_len: uint8)
    returns (x: Err<(connection_id_fixed, uint32)>)
    requires buffer_valid(packet, packet_len);
    ensures x.Ok? ==> parse_offset <= x.value.1;
{
    if parse_offset > packet_len { return Fail("parse_offset makes no sense"); }
    if packet_len - parse_offset < cid_len as uint32 { return Fail("insufficient buffer space"); }
    if cid_len > 20 { return Fail("cid_len makes no senese"); }

    var buffer := new byte[cid_len];
    var temp := getbytes_s(packet, packet_len, parse_offset, buffer, cid_len as uint32);
    if temp.Fail? {return Fail("failed to decode cid"); }

    var cid :connection_id_fixed := connection_id_raw(buffer[..], cid_len);
    return Ok((cid, temp.value));
}

method decode_connection_id(packet: buffer_t, packet_len: uint32, initial_offset: uint32)
    returns (x: Err<(connection_id_fixed, uint32)>)
    requires buffer_valid(packet, packet_len);
    ensures x.Ok? ==> initial_offset < x.value.1;
{
    if initial_offset >= packet_len { return Fail("insufficient buffer space"); }

    var cid_len := packet[initial_offset] as uint8;
    var parse_offset := initial_offset + 1;

    x := parse_connection_id(packet, packet_len, parse_offset, cid_len);
}

// (** Process a Version Negotation packet *)
method processVersionNegotiation (cs: connection, packet:buffer_t, packet_len:uint32, initial_offset:uint32)
    returns (x :Err<uint32>)

    requires buffer_valid(packet, packet_len);
    ensures buffer_offset_valid_pos(packet_len, initial_offset, x);
{
    if initial_offset != 0 { return Fail("version negotiation packet not starting at 0?"); }

    var parse_offset := 5;
    var dcid, scid;

    var temp_0 := decode_connection_id(packet, packet_len, parse_offset);
    if temp_0.Fail? { return Fail("decoding dcid failed"); }
    dcid, parse_offset := temp_0.value.0, temp_0.value.1;

    var temp_1 := decode_connection_id(packet, packet_len, parse_offset);
    if temp_1.Fail? { return Fail("decoding scid failed"); }
    scid, parse_offset := temp_1.value.0, temp_1.value.1;

    while parse_offset < packet_len
    {
        if packet_len - parse_offset < 4 { return Fail("insufficient space in version negotiation packet"); }
        var version := getu32(packet, parse_offset);
        print("[DEBUG DFY] supported version: ", version, "\n");
        parse_offset := parse_offset + 4;
    }

    return Fail ("Unsupported QUIC version from the peer");
}

method decode_client_initial_packet_partial(packet: buffer_t, packet_len:uint32)
    returns (x: Err<(connection_id_fixed, connection_id_fixed, uint32)>)
    requires buffer_valid(packet, packet_len);
{
    if packet_len <= 5 {
        return Fail("insufficient space in initial packet");
    }

    var version := getu32(packet, 1);
    var parse_offset : uint32:= 5;
    var dcid, scid;

    var temp0 := decode_connection_id(packet, packet_len, parse_offset);
    if temp0.Fail? { return Fail("decoding dcid failed"); }
    dcid, parse_offset := temp0.value.0, temp0.value.1;

    var temp1 := decode_connection_id(packet, packet_len, parse_offset);
    if temp1.Fail? { return Fail("decoding dcid failed"); }
    scid, parse_offset := temp1.value.0, temp1.value.1;

    return Ok((scid, dcid, version));
}

method process_client_initial_packet_impl(cs: connection, dcid: connection_id_fixed, packet:buffer_t, packet_len:uint32)
    returns (x: Err<uint32>)

    requires buffer_valid(packet, packet_len);
    requires cs.Valid();
    modifies cs`ready, cs`epoch, cs`cstate, cs`mitls_reader_key, cs`mitls_writer_key;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.ps_states_repr;

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager`total_data_sent,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`stream_nodes_repr;

    modifies packet;

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    ensures cs.Valid();
{
    var temp_0 := cs.pspace_manager.decrypt_pakcet(INITIAL_SPACE, dcid.len, packet, packet_len, 0); 
    if temp_0.Fail? { return Fail("decryption failed"); }
    var result := temp_0.value;
    cs.cstate := Running;

    var offset_op := process_client_initial_frames(cs, packet, result.end_offset, result.start_offset);

    if offset_op.Ok? {
        x := Ok(result.next_packet_offset);
    } else {
        x := Fail("failed to decode inital pakcet");
    }
}

// (** Process a received Handshake packet *)
method process_handshake_packet(cs: connection, packet:buffer_t, packet_len:uint32, offset: uint32) returns (x :Err<uint32>)
    requires cs.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, offset);

    modifies cs`ready, cs`epoch, cs`cstate, cs`mitls_reader_key, cs`mitls_writer_key;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.ps_states_repr;

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager`total_data_sent,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`stream_nodes_repr;

    modifies packet;

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    ensures buffer_offset_valid_pos(packet_len, offset, x);
    ensures cs.Valid();
{
    var temp_0 := cs.pspace_manager.decrypt_pakcet(HANDSHAKE_SPACE, ENGINE_CIL, packet, packet_len, offset);
    if temp_0.Fail? { return Fail("decryption failed"); }
    var result := temp_0.value;

    var temp_1 := process_handshake_or_initial_frames(cs, HANDSHAKE_SPACE, packet, result.end_offset, result.start_offset);
    if temp_1.Fail? {return Fail(temp_1.err);}

    return Ok(result.next_packet_offset);
}

// (** Process a received Initial packet *)
method process_initial_packet(cs: connection, packet:buffer_t, packet_len:uint32, offset: uint32) returns (x :Err<uint32>)
    requires cs.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, offset);

    modifies cs`ready, cs`epoch, cs`cstate,
        cs`mitls_reader_key, cs`mitls_writer_key, 
        cs`dst_connection_id;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.ps_states_repr;

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager`total_data_sent,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`stream_nodes_repr;

    modifies packet;

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    ensures buffer_offset_valid_pos(packet_len, offset, x);
    ensures cs.Valid();
{
    print("[DEBUG DFY] processing initial packet\n");
    var temp_0 := cs.pspace_manager.decrypt_pakcet(INITIAL_SPACE, ENGINE_CIL, packet, packet_len, offset);
    if temp_0.Fail? { return Fail("decryption failed"); }
    var result := temp_0.value;

    cs.update_dcid(result.cid);

    var temp_1 := process_handshake_or_initial_frames(cs, INITIAL_SPACE, packet, result.end_offset, result.start_offset);
    if temp_1.Fail? {return Fail(temp_1.err);}

    return Ok(result.next_packet_offset);
}

// (** Process a received long-header packet *)
method process_long_header_packet(cs: connection, packet:buffer_t, packet_len:uint32, offset: uint32)
    returns (x : Err<uint32>)
    requires cs.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, offset);

    modifies cs`ready, cs`epoch, cs`cstate,
        cs`mitls_reader_key, cs`mitls_writer_key, 
        cs`dst_connection_id;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.ps_states_repr;

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager`total_data_sent,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`stream_nodes_repr;

    modifies packet;

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    ensures cs.Valid();
    ensures buffer_offset_valid_pos(packet_len, offset, x);
{
    if packet_len - offset <= 5 { return Fail("insufficient space in packet buffer");}

    var packet_type := get_packet_type(packet[offset]);

    var version := getu32(packet, 1);

    if version != quicVersion {
        if version == 0 {
            var temp := processVersionNegotiation(cs, packet, packet_len, offset);
            return temp;
        }
        // v=0ul should have been handled by processClientInitial, for the handshake.
        // connection resumption might mean we have to renegotiate version here too.
        return Fail("Unexpected QUIC version");
    }

    if packet_type == INITIAL_TYPE { x := process_initial_packet(cs, packet, packet_len, offset);}  // Initial
    else if packet_type == RETRY_TYPE { x := Fail("Unsupported - Retry"); } // Retry
    else if packet_type == HANDSHAKE_TYPE { x := process_handshake_packet(cs, packet, packet_len, offset); } // Handshake
    else if packet_type == ZERORTT_TYPE { x := Fail("Unsupported - 0-RTT Protected"); } // 0-RTT Protected
    else { x := Fail("Unsupported long header type");}
}

/* Process multiple QUIC packets within a single UDP packet.    There can be one or more
         long header packets followed by a single short header packet, all together. */

method process_long_header_packets (cs: connection, packet:buffer_t, packet_len:uint32) returns (x:Err<uint32>)
    requires cs.Valid();
    requires buffer_valid(packet, packet_len);

    modifies cs`ready, cs`epoch, cs`cstate, cs`mitls_reader_key, cs`mitls_writer_key, cs`dst_connection_id;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.ps_states_repr;

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager`total_data_sent,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`stream_nodes_repr;

    modifies packet;

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    ensures cs.Valid();
{
    var parse_offset :uint32 := 0;

    while parse_offset < packet_len
        invariant cs.Valid();
        invariant fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))
        invariant fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr))
        invariant fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr))
        invariant fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
        invariant buffer_offset_valid_pre(packet, packet_len, parse_offset);
        invariant cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    {
        var flag := packet[parse_offset];
        var long_header := is_long_header_packet(flag);
        if ! long_header {
            return Ok(parse_offset); // stop looping, as a short packet has been found
        }

        var temp := process_long_header_packet(cs, packet, packet_len, parse_offset);
        if temp.Fail? { return Fail(temp.err); }
        parse_offset := temp.value;
        if parse_offset == packet_len {
            break;
        }
    }

    x := Ok(parse_offset);
}

method {:timeLimit 50} process_short_header_packet_impl (cs: connection, packet: buffer_t, packet_len:uint32, offset:uint32)
    returns (x:Err<uint32>)

    requires cs.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, offset);

    modifies cs`epoch, cs`cstate, cs`ready, cs`mitls_reader_key, cs`mitls_writer_key;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager.ps_states_repr, 
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr;

    modifies cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr,
        cs.stream_manager`peer_streams_bidi,
        cs.stream_manager`peer_streams_uni,
        cs.stream_manager`peer_max_data,
        cs.stream_manager`total_data_sent,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`segment_lists_repr,
        cs.stream_manager`quic_streams_repr,
        cs.stream_manager`peer_max_streams_bidi,
        cs.stream_manager`peer_max_streams_uni,
        cs.stream_manager`stream_nodes_repr;
    
    modifies packet;

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
    ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));

    ensures cs.Valid();
{
    var temp_0 := cs.pspace_manager.decrypt_pakcet(APPLICATION_SPACE, ENGINE_CIL, packet, packet_len, offset);
    if temp_0.Fail? { return Fail("decryption failed"); }
    var result := temp_0.value;

    var processed_op := process_short_header_frames(cs, packet, result.end_offset, result.start_offset);
    if processed_op.Fail? {return Fail(processed_op.err);}
    var processed := processed_op.value;

    cs.pspace_manager.register_packet_space_ack(APPLICATION_SPACE, result.pn, processed.ack_eliciting);

    return Ok(result.end_offset);
}

method process_buffered_short_header_packets(cs: connection)
    requires cs.Valid();

    modifies cs`epoch, cs`cstate, cs`ready, cs`mitls_reader_key, cs`mitls_writer_key;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager.ps_states_repr, 
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr;

    modifies cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr,
        cs.stream_manager`peer_streams_bidi,
        cs.stream_manager`peer_streams_uni,
        cs.stream_manager`peer_max_data,
        cs.stream_manager`total_data_sent,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`segment_lists_repr,
        cs.stream_manager`quic_streams_repr,
        cs.stream_manager`peer_max_streams_bidi,
        cs.stream_manager`peer_max_streams_uni,
        cs.stream_manager`stream_nodes_repr;

    modifies cs.short_header_packets`current_size;
    
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
    ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr))
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));

    ensures cs.Valid();
{
    var size := cs.short_header_packets.get_size();
    var short_header_packets := cs.short_header_packets.buffer[..size]; // conversion expensive
    cs.short_header_packets.clear();

    var key_ready := cs.pspace_manager.crypto_state_ready(APPLICATION_SPACE);

    if !key_ready || size == 0 {
        return;
    }

    var i := 0;
    while i < size
        invariant cs.Valid();
        invariant cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
        invariant fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr))
        invariant fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr))
        invariant fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))
        invariant fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr))
        invariant fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr))
        invariant fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    {
        var packet_holder: packet_holder_fixed := short_header_packets[i];
        var packet_len := packet_holder.packet_len;
        var packet := build_buffer_from_seq(packet_holder.packet, packet_len);
        var result := process_short_header_packet_impl(cs, packet, packet_len, 0);
        match result {
            case Ok (x) => {}
            case Fail(s) => print("[DEBUG DFY] Catching up with short header packet Fail: ", s, "\n");
        }
        i := i + 1;
    }
}

method process_short_header_packet (cs: connection, packet:buffer_t, packet_len:uint32, offset: uint32)
    returns (x :Err< uint32>)
    requires cs.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, offset);

    modifies cs`epoch, cs`cstate, cs`ready, cs`mitls_reader_key, cs`mitls_writer_key;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager.ps_states_repr, 
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr;

    modifies cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr,
        cs.stream_manager`peer_streams_bidi,
        cs.stream_manager`peer_streams_uni,
        cs.stream_manager`peer_max_data,
        cs.stream_manager`total_data_sent,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`segment_lists_repr,
        cs.stream_manager`quic_streams_repr,
        cs.stream_manager`peer_max_streams_bidi,
        cs.stream_manager`peer_max_streams_uni,
        cs.stream_manager`stream_nodes_repr;

    modifies packet;

    modifies cs.short_header_packets, cs.short_header_packets.buffer;
    
    ensures cs.short_header_packets.buffer == old(cs.short_header_packets.buffer) || fresh(cs.short_header_packets.buffer);
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
    ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr))

    ensures cs.Valid();
{
    var key_ready := cs.pspace_manager.crypto_state_ready(APPLICATION_SPACE);

    if !key_ready {
        print ("[DEBUG DFY] Buffering key1 packet for later\n");
        var t :packet_holder_fixed := packet_holder_raw(packet[offset..packet_len], packet_len - offset);
        cs.short_header_packets.push_back(t);
        x := Ok(0);
    } else {
        x := process_short_header_packet_impl(cs, packet, packet_len, offset);
    }
}

method connection_process_coalesced_packets(cs: connection, packet:buffer_t, packet_len:uint32)
    returns (x: Err<uint32>)

    requires cs.Valid();
    requires buffer_valid(packet, packet_len);

    modifies cs`epoch, cs`cstate, cs`ready, cs`mitls_reader_key, cs`mitls_writer_key, cs`dst_connection_id;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager.ps_states_repr, 
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr;

    modifies cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr,
        cs.stream_manager`peer_streams_bidi,
        cs.stream_manager`peer_streams_uni,
        cs.stream_manager`peer_max_data,
        cs.stream_manager`total_data_sent,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`segment_lists_repr,
        cs.stream_manager`quic_streams_repr,
        cs.stream_manager`peer_max_streams_bidi,
        cs.stream_manager`peer_max_streams_uni,
        cs.stream_manager`stream_nodes_repr;
    
    modifies cs.short_header_packets, cs.short_header_packets.buffer;

    modifies packet;
    
    ensures cs.short_header_packets.buffer == old(cs.short_header_packets.buffer) || fresh(cs.short_header_packets.buffer);
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
    ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr))

    ensures cs.Valid();
{
    print("[DEBUG DFY] connection_process_coalesced_packets enter\n");

    var temp := process_long_header_packets(cs, packet, packet_len);

    if temp.Fail? {
        print("[DEBUG DFY] connection_process_coalesced_packets fail\n");
        return Fail(temp.err);
    }

    var parese_offset := temp.value;
    if parese_offset < packet_len {
        x := process_short_header_packet(cs, packet, packet_len, parese_offset);
    } else {
        x := Ok(parese_offset);
    }
    print("[DEBUG DFY] connection_process_coalesced_packets ok\n");
}

function method is_long_header_packet(flag: uint8) : (x: bool)
{
    and8(flag, LONG_HEADER_MASK) == LONG_HEADER_MASK
}

method get_packet_type(flag: uint8) returns (x: uint2)
{
  x := and8(flag / 16, 0x3) as uint2;
  print("[DEBUG DFY] flag = ", flag,", get_packet_type = ", x, "\n");
}

method {:timeLimit 50} connection_process_packet_impl(cs: connection, long_header: bool, packet:buffer_t, packet_len:uint32)
    returns (x :Err<uint32>)

    requires cs.Valid();
    requires buffer_valid(packet, packet_len);

    modifies cs`epoch, cs`cstate, cs`ready, cs`mitls_reader_key, cs`mitls_writer_key, cs`dst_connection_id;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager.ps_states_repr, 
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr;

    modifies cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr,
        cs.stream_manager`peer_streams_bidi,
        cs.stream_manager`peer_streams_uni,
        cs.stream_manager`peer_max_data,
        cs.stream_manager`total_data_sent,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`segment_lists_repr,
        cs.stream_manager`quic_streams_repr,
        cs.stream_manager`peer_max_streams_bidi,
        cs.stream_manager`peer_max_streams_uni,
        cs.stream_manager`stream_nodes_repr;
    
    modifies cs.short_header_packets, cs.short_header_packets.buffer;

    modifies packet;
    
    ensures cs.short_header_packets.buffer == old(cs.short_header_packets.buffer) || fresh(cs.short_header_packets.buffer);
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
    ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));

    ensures cs.Valid();
{
    if long_header {
        x := connection_process_coalesced_packets(cs, packet, packet_len);
        process_buffered_short_header_packets(cs);
    } else {
        x := process_short_header_packet(cs, packet, packet_len, 0);
    }
}

method {:timeLimit 50} connection_process_packet(cs: connection, packet:buffer_t, packet_len:uint32)
    returns (x :Err<uint32>)

    requires cs.Valid();
    requires buffer_valid(packet, packet_len);

   modifies cs`epoch, cs`cstate, cs`ready, cs`mitls_reader_key, cs`mitls_writer_key, cs`dst_connection_id;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager.ps_states_repr, 
        cs.pspace_manager.ack_buffers_repr,
        cs.pspace_manager.crypto_states_repr,
        cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr;

    modifies cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.stream_lists_repr,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr,
        cs.stream_manager`peer_streams_bidi,
        cs.stream_manager`peer_streams_uni,
        cs.stream_manager`peer_max_data,
        cs.stream_manager`total_data_sent,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`segment_lists_repr,
        cs.stream_manager`quic_streams_repr,
        cs.stream_manager`peer_max_streams_bidi,
        cs.stream_manager`peer_max_streams_uni,
        cs.stream_manager`stream_nodes_repr;
    
    modifies cs.short_header_packets, cs.short_header_packets.buffer;

    modifies packet;
    
    ensures cs.short_header_packets.buffer == old(cs.short_header_packets.buffer) || fresh(cs.short_header_packets.buffer);
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
    ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));

    ensures cs.Valid();
{
    var long_header := is_long_header_packet(packet[0]);

    cs.enter_monitor();
    x := connection_process_packet_impl(cs, long_header, packet, packet_len);
    cs.update_send_data_ready();
    cs.exit_monitor();
}

method set_max_streams(cs: connection, bidi: bool, max_streams: uint62)
    returns (x:handle_t) // (* a waitable handle *)
    requires cs.Valid();

    modifies cs`cstate, cs`ready;

    modifies cs.stream_manager`local_max_streams_bidi,
        cs.stream_manager`local_max_streams_uni;

    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);


    ensures cs.Valid();
{
    x := NONE_HANDLE;

    if cs.cstate == Start { return; }

    if bidi {
        if cs.stream_manager.local_max_streams_bidi >= max_streams { return; }
        cs.stream_manager.local_max_streams_bidi := max_streams;
    } else {
        if cs.stream_manager.local_max_streams_uni >= max_streams { return; }
        cs.stream_manager.local_max_streams_uni := max_streams;
    }

    var frame := create_MAX_STREAMS_frame(bidi, max_streams);
    x := cs.enqueue_fixed_frame(frame);
    cs.update_send_data_ready();
}

method set_max_data (cs: connection, max_data: uint62) returns (x: handle_t) // (* a waitable handle *)
    requires cs.Valid();

    modifies cs`cstate, cs`ready;
    modifies cs.stream_manager`local_max_data;

    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    ensures cs.Valid();
{
    x := NONE_HANDLE;

    if cs.cstate == Start { return; }

    if cs.stream_manager.local_max_data >= max_data { return; }
    cs.stream_manager.local_max_data := max_data;

    var frame := create_MAX_DATA_frame(max_data);
    x := cs.enqueue_fixed_frame(frame);
    cs.update_send_data_ready();
}

}
