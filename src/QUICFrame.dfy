include "Options.dfy"
include "NativeTypes.dfy"
include "QEngine.dfy"
include "QUICUtils.dfy"
include "QUICTLS.dfy"
include "QUICFFI.dfy"
include "QUICStream.dfy"
include "QUICLossAndCongestion.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"

include "HandleFFIs.dfy"
include "QStream.dfy"
include "QStreamManager.dfy"
include "QLossRecovery.dfy"
include "QPacketSpace.dfy"
include "QConnection.dfy"
include "Extern.dfy"

module QUICFrame {
import opened Options
import opened NativeTypes
import opened QEngine
import opened QUICUtils
import opened QUICTLS
import opened QUICFFI
import opened QUICStream
import opened QUICLossAndCongestion
import opened QUICDataTypes
import opened QUICConstants
import opened HandleFFIs
import opened QStream
import opened QStreamManager
import opened QLossRecovery
import opened QPacketSpace
import opened QConnection
import opened Extern


// Prepare one frame of stream data from a segment, having already confirmed that the frame and segment fit entirely in the frame.
method encode_stream_frame(
    stream_id:stream_id_t,
    segment:qstream_segment_fixed,
    packet:buffer_t, packet_len: uint32, p:uint32,
    lrlist:loss_tracker_list)
    returns (x : uint32)

    requires lrlist.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, p);

    requires (packet_len as int - p as int) >= 25 + segment.datalength as int;

    modifies lrlist, lrlist.Repr;
    modifies packet;

    ensures lrlist.Valid();
    ensures p < x <= packet_len  // can be equal
    ensures fresh(lrlist.Repr - old(lrlist.Repr));
{
    var tracker := stream_tracker(segment);
    lrlist.InsertTail(tracker);

    var segment_offset := segment.offset;
    var data_length := segment.datalength;
    var fin := segment.fin;

    var o : uint8 := if segment_offset == 0 then 0x00 else 0x04; // OFF bit
    var f := if fin then 0x01 else 0x00; // FIN bit

    var s := or8(0x8, 0x02);  // LEN
    s := or8(f, s); // FIN
    s := or8(o, s); // OFF

    if fin {
        print("[DEBUG DFY] sending last segment");
    }

    // Produce a STREAM frame
    var p := append8(packet, p, s);
    p := encode_variable_strict(packet, p, stream_id);

    if segment_offset != 0 {
        p := encode_variable_strict(packet, p, segment_offset);
    }

    p := encode_variable_strict(packet, p, data_length as uint62);
    p := append_sequence(packet, p, segment.data, data_length);

    return p;
}

method create_MAX_STREAMS_frame(bidi: bool, max_streams: uint62) returns (frame :fixed_frame_fixed)
{
    var frame_type := if bidi then MAX_STREAMS_BIDI_TYPE else MAX_STREAMS_UNI_TYPE;
    var len := 1 + encoded_size_strict(max_streams);
    var data := new byte[len];
    var offset := append8 (data, 0, frame_type);
    offset := encode_variable_strict(data, offset, max_streams);
    var handle := create_event_handle(0, 0);
    frame := fixed_frame_raw(data[..], offset, handle);
}

method create_RESET_STREAM_frame(stream: quic_stream_mutable, err: uint16) returns (frame :fixed_frame_fixed)
{
    var final_size := stream.nextWriteOffset;
    var stream_id := stream.stream_id;
    var len := 1 + encoded_size_strict(stream_id) + 2 + encoded_size_strict(final_size);
    var data := new byte[len];

    var offset := append8(data, 0, RESET_STREAM_TYPE);
    offset := encode_variable_strict(data, offset, stream_id);
    offset := append16(data, offset, err); // Error Code
    offset := encode_variable_strict(data, offset, final_size);

    var handle := create_event_handle(0, 0);
    frame := fixed_frame_raw(data[..], offset, handle);
}

method create_MAX_DATA_frame(value: uint62)  returns (frame :fixed_frame_fixed)
{
    var len := 1 + encoded_size_strict(value);
    var data := new byte[len];
    var offset := append8 (data, 0, MAX_DATA_TYPE);
    offset := encode_variable_strict (data, offset, value);

    var handle := create_event_handle(0, 0);
    frame := fixed_frame_raw(data[..], offset, handle);
}

// (** Prepare a PING frame *)
method prepare_ping_frame(packet:buffer_t, packet_len:uint32, p:uint32)
    returns (x :uint32)
    requires buffer_offset_valid_pre(packet, packet_len, p)
    modifies packet
    ensures x == p + 1;
{
    print("[DEBUG DFY] Preparing PING\n");
    x := append8(packet, p, PING_TYPE);
}

method encode_crypto_frame (segment:qstream_segment_fixed,
        packet:buffer_t,
        packet_len:uint32,
        p:uint32,
        lrlist:loss_tracker_list)
    returns (y: uint32)

    requires buffer_offset_valid_pre(packet, packet_len, p);
    requires lrlist.Valid();

    modifies packet;
    modifies lrlist, lrlist.Repr;

    ensures fresh(lrlist.Repr - old(lrlist.Repr))
    ensures lrlist.Valid();
    ensures p < y <= packet_len;
{
    var segment_offset := segment.offset;
    var data := segment.data;
    var data_length := segment.datalength;

    var available_length := packet_len - p; // how many bytes available in the packet
    if available_length < 17 {
        fatal ("Crypto frame header doen't fit in the packet");
    }

    print("[DEBUG DFY] preparing CRYPTO frame ", data_length, "\n");

    available_length := available_length - 17;

    if available_length < data_length {
        fatal ("Crypto frame data doen't fit in the packet");
    }

    if segment_offset as uint64 > UINT62_MAX {
        fatal ("invalid segment_offset");
    }

    assert data_length as int + 17 <= packet_len as int - p as int;

    var p := append8(packet, p, CRYPTO_TYPE);
    p := encode_variable_strict(packet, p, segment_offset as uint62);
    p := encode_variable_strict(packet, p, data_length as uint62);
    p := append_sequence(packet, p, data, data_length);

    var tracker := crypto_tracker(segment);
    lrlist.InsertTail(tracker);

    y := p;
}

method encode_ack_blocks(
        ack_blocks:seq<ackblock_fixed>,
        block_count:uint32,
        packet:buffer_t,
        packet_len:uint32,
        p:uint32)
    returns (x: uint32)

    requires |ack_blocks| == block_count as int && block_count >= 2;
    requires buffer_offset_valid_pre(packet, packet_len, p)
    modifies packet
    ensures p <= x <= packet_len  // can be equal
{
    var i, ack_block := 1, ack_blocks[1]; // need to skip over the first one
    var packet_offset := p;

    while i < block_count
        invariant p <= packet_offset <= packet_len
        invariant buffer_offset_valid_pre(packet, packet_len, packet_offset);
    {
        var gap := ack_block.gap;

        var available_length := packet_len - packet_offset; // how many bytes available in the packet

        if available_length < 16 {
            fatal("not enough sapce in ack frame"); // fatal error
            return;
        }
        if gap == 0 { fatal("gap should not be zero here"); }
        // The number of packets in the gap is one higher than the encoded value of the Gap field.
        packet_offset := encode_variable_strict(packet, packet_offset, gap - 1);
        packet_offset := encode_variable_strict(packet, packet_offset, ack_block.range);

        if packet_offset >= packet_len {
            fatal("not enough sapce in ack frame");
            return;
        }

        i := i + 1;
    }

    x := packet_offset;
}

method encode_ack_frame(pss:packet_space_state,
    pn_space: packet_space,
    packet:buffer_t,
    packet_len:uint32,
    p:uint32,
    lrlist:loss_tracker_list)

    returns (x:uint32)

    requires buffer_offset_valid_pre(packet, packet_len, p)
    requires pss.Valid()
    requires lrlist.Valid()

    modifies pss`ack_only_packet,
        pss`outgoging_ack_count,
        pss`ack_eliciting;

    modifies packet
    modifies lrlist, lrlist.Repr

    ensures lrlist.Valid()
    ensures pss.Valid()
    ensures fresh(lrlist.Repr - old(lrlist.Repr))
    ensures p <= x <= packet_len;  // can be equal
{
    if pss.outgoging_ack_count == 0 {
        print("[DEBUG DFY] Preparing ACK frame: No outgoing ACKs\n");
        return p;
    }

    var available_length := packet_len - p; // how many bytes available in the packet

    if available_length < 33 {
        fatal("not enough sapce for ack frame header");
        return;
    }

    var ack_frame := pss.build_ack_blocks(pn_space);
    pss.reset_ack_buffer();

    var count := ack_frame.block_count;
    var ack_blocks := ack_frame.ack_blocks;

    var firstblock : ackblock_fixed := ack_blocks[0];
    var largest_ackednowledged := firstblock.start;
    var ack_delay := 10000;

    x := append8(packet, p, ACK_NON_ECN_TYPE);
    x := encode_variable_strict(packet, x, largest_ackednowledged);
    x := encode_variable_strict(packet, x, ack_delay);
    x := encode_variable_strict(packet, x, (count - 1) as uint62);
    x := encode_variable_strict(packet, x, firstblock.range); // First ACK Block

    if count != 1 {
        x := encode_ack_blocks(ack_blocks, count, packet, packet_len, x);
    }

    var ack_tracker := ack_tracker(ack_frame);
    lrlist.InsertTail(ack_tracker);
}

method prepare_ack_frame(cs: connection,
    ps:packet_space,
    packet:buffer_t,
    packet_len:uint32,
    p:uint32,
    lrlist:loss_tracker_list)
    returns (x:uint32)

    requires buffer_offset_valid_pre(packet, packet_len, p)
    requires cs.Valid()
    requires lrlist.Valid()

    modifies cs.pspace_manager.ps_states_repr;

    modifies packet
    modifies lrlist, lrlist.Repr

    ensures lrlist.Valid()
    ensures cs.Valid()
    ensures fresh(lrlist.Repr - old(lrlist.Repr))
    ensures p <= x <= packet_len;  // can be equal
{
    var pss := cs.pspace_manager.get_packet_space_state(ps);
    x := encode_ack_frame(pss, ps, packet, packet_len, p, lrlist);
}

method decode_ack_block (packet:buffer_t, packet_len:uint32, offset:uint32)
    returns (x:Err<(uint62, uint62, uint32)>)

    requires packet != null && packet_len as int <= packet.Length;
{
    var ack_range, gap, offset;

    var temp_0 := decode_variable_loose(packet, packet_len, offset);
    if temp_0.Fail? { return Fail(temp_0.err); }
    gap, offset := temp_0.value.0, temp_0.value.1;

    var temp_1 := decode_variable_loose(packet, packet_len, offset);
    if temp_1.Fail? { return Fail(temp_1.err); }
    ack_range, offset := temp_1.value.0, temp_1.value.1;

    return Ok((gap, ack_range, offset));
}

method decode_ACK_frame_header(packet:buffer_t, packet_len:uint32, offset:uint32)
    returns (x: Err<(uint62, uint62, uint62, uint62, uint32)>)

    requires buffer_offset_valid_pre(packet, packet_len, offset);
    ensures x.Ok? ==> offset < x.value.4 <= packet_len  // can be equal
{
    if offset == UINT32_MAX { return Fail("invalid offset"); }

    var largest_acked, ack_delay, block_count, first_ack_range;
    var offset' := offset;

    var temp_0 := decode_variable_loose(packet, packet_len, offset');
    if temp_0.Fail? { return Fail(temp_0.err); }
    largest_acked, offset' := temp_0.value.0, temp_0.value.1;

    var temp_1 := decode_variable_loose(packet, packet_len, offset');
    if temp_1.Fail? { return Fail(temp_1.err); }
    ack_delay, offset' := temp_1.value.0, temp_1.value.1;

    var temp_2 := decode_variable_loose(packet, packet_len, offset');
    if temp_2.Fail? { return Fail(temp_2.err); }
    block_count, offset' := temp_2.value.0, temp_2.value.1;

    var temp_3 := decode_variable_loose(packet, packet_len, offset');
    if temp_3.Fail? { return Fail(temp_3.err);}
    first_ack_range, offset' := temp_3.value.0, temp_3.value.1;

    return Ok((largest_acked, ack_delay, block_count, first_ack_range, offset'));
}

method decode_ack_ranges(ps: packet_space, packet:buffer_t, packet_len:uint32, offset:uint32)
    returns (x: Err<(ack_frame_fixed, uint32)>)

    requires buffer_offset_valid_pre(packet, packet_len, offset);
{
    var temp_0 := decode_ACK_frame_header(packet, packet_len, offset);
    if temp_0.Fail? { return Fail("unable to decode ack frame header"); }
    var largest_acked, ack_delay, block_count, first_ack_range, offset :=
        temp_0.value.0, temp_0.value.1, temp_0.value.2, temp_0.value.3, temp_0.value.4;

    if largest_acked < first_ack_range { return Fail("Largest Acknowledged is less than First ACK Range"); }
    if block_count >= (UINT32_MAX -1) as uint62 { return Fail("block_count too large"); }

    var ack_ranges := new ackblock_fixed[block_count + 1];

    var largest := largest_acked;
    var smallest :=  largest - first_ack_range;
    ack_ranges[0] := ack_block_raw(0, largest_acked, first_ack_range);

    var gap, ack_range;
    var bn := 0;

    while bn < block_count
    {
        var temp_1 := decode_ack_block(packet, packet_len, offset);
        if temp_1.Fail? { return Fail("unable to decode ack block"); }

        gap, ack_range, offset := temp_1.value.0, temp_1.value.1, temp_1.value.2;

        // From RFC: The number of packets in the gap is one higher than the encoded value of the Gap field.
        if smallest < gap || smallest - gap < 2 { return Fail("unable to decode ack block"); }
        largest := smallest - gap - 2; // smallest from the previous

        if largest < ack_range { return Fail("unable to decode ack block"); }
        smallest := largest - ack_range;

        ack_ranges[bn + 1] := ack_block_raw(0, largest, ack_range);
        bn := bn + 1;
    }

    var ack_frame :ack_frame_fixed := ack_frame_raw(ack_ranges[..], block_count as uint32 + 1, ack_delay, ps);
    return Ok((ack_frame, offset));
}

// Process an ACK frame
method process_ACK_frame (cs:connection,
    pn_space: packet_space,
    packet:buffer_t,
    packet_len:uint32,
    offset:uint32,
    frame_type:uint8)
    returns (x:Err<uint32>)

    requires buffer_offset_valid_pre(packet, packet_len, offset);
    requires cs.Valid();

    modifies cs`cstate, cs`ready;

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
        cs.pspace_manager.ack_buffers_repr;

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`total_data_sent;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr))

    ensures cs.Valid();
    ensures buffer_offset_valid_pos(packet_len, offset, x);
{
    if frame_type != ACK_NON_ECN_TYPE { return Fail("ECN flag not supported"); }
    var temp := decode_ack_ranges(pn_space, packet, packet_len, offset);
    if temp.Fail? { return Fail("failed to decode ackranges"); }
    var ack_frame, new_offset := temp.value.0, temp.value.1;
    cs.process_ack_frame_impl(ack_frame);
    if ! (offset < new_offset <= packet_len) { fatal("something wrong with ack frame decoding"); }

    return Ok(new_offset);
}

method decode_RESET_STREAM_frame(packet:buffer_t, packet_len:uint32, initial_offset:uint32)
    returns (x:Err<(uint62, uint62, uint62, uint32)>)
    requires buffer_offset_valid_pre(packet, packet_len, initial_offset);
    ensures x.Ok? ==> initial_offset < x.value.3 <= packet_len  // can be equal
{
    var temp_0 := decode_variable_loose(packet, packet_len, initial_offset);
    if temp_0.Fail? { return Fail("cannot decode stream_id"); }
    var stream_id, final_size, error_code, offset;
    stream_id, offset := temp_0.value.0, temp_0.value.1;

    var temp_1 := decode_variable_loose(packet, packet_len, offset);
    if temp_1.Fail? { return Fail("cannot decode err_ocode");}
    error_code, offset := temp_1.value.0, temp_1.value.1;

    var temp_2 := decode_variable_loose(packet, packet_len, offset);
    if temp_2.Fail? { return Fail("cannot decode err_ocode");}
    final_size, offset := temp_2.value.0, temp_2.value.1;
    return Ok((stream_id, error_code, final_size, offset));
}

// (** Parse RST_STREAM *)
method process_RESET_STREAM_frame (cs:connection, packet:buffer_t, packet_len:uint32, offset:uint32) returns (x:Err<uint32>)
    requires cs.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, offset);

    modifies
        cs.stream_manager`peer_streams_bidi,
        cs.stream_manager`peer_streams_uni,
        cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`segment_lists_repr,
        cs.stream_manager`quic_streams_repr;
    modifies
        cs.stream_manager.quic_streams_repr;

    modifies cs.stream_manager.stream_lists_repr,
        cs.stream_manager.stream_nodes_repr;
    modifies cs.stream_manager`stream_nodes_repr;

    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))
    ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr))
    ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr))
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));

    ensures buffer_offset_valid_pos(packet_len, offset, x);
    ensures cs.Valid();
{
    var temp := decode_RESET_STREAM_frame(packet, packet_len, offset);
    if temp.Fail? { return Fail("error decoding "); }
    var stream_id, error_code, final_size := temp.value.0, temp.value.1, temp.value.2;
    cs.stream_manager.reset_stream(stream_id, error_code, final_size);
    return Ok(temp.value.3);
}

// (** decode a CRYPTO frame into a stream segment *)
method decode_CRYPTO_frame(packet:buffer_t, packet_len:uint32, initial_offset:uint32)
    returns (x :Err <(qstream_segment_fixed, uint32)>)
    requires buffer_offset_valid_pre(packet, packet_len, initial_offset);
    ensures x.Ok? ==> initial_offset < x.value.1 <= packet_len;  // can be equal
{
    print("[DEBUG DFY] decode_CRYPTO_frame start\n");

    var stream_offset, data_length, offset;
    var temp_0 := decode_variable_loose(packet, packet_len, initial_offset);
    if temp_0.Fail? { return Fail(temp_0.err); }

    stream_offset, offset := temp_0.value.0, temp_0.value.1;

    var temp_1 := decode_variable_loose(packet, packet_len, offset );
    if temp_1.Fail? { return Fail(temp_1.err); }
    if temp_1.value.0 > UINT32_MAX as uint62 { return Fail("invalid data length"); }
    data_length, offset := temp_1.value.0 as uint32, temp_1.value.1;

    if data_length as uint64 > UINT16_MAX as uint64 { return Fail("Stream data length too long"); }

    if data_length > packet_len - offset { return Fail("Stream data length too long");}

    print("[DEBUG DFY] decoding crypto frame offset=", stream_offset, " length=", data_length, "\n");

    var seg_data := new byte[data_length];
    blit(packet, offset, seg_data, 0, data_length);

    if stream_offset as uint64 + data_length as uint64 > UINT62_MAX {
        return Fail("segment_offset makes no sense");
    }

    var segment : qstream_segment_fixed :=
        qstream_segment_raw(stream_offset, seg_data[..], data_length, false, false, 0, 0xffff);
    offset := offset + data_length;

    return Ok((segment, offset));
}

method process_CRYPTO_frame (cs:connection, ps:packet_space, packet:buffer_t, packet_len:uint32, offset:uint32) returns (x:Err<uint32>)

    requires buffer_offset_valid_pre(packet, packet_len, offset);
    requires cs.Valid();

    modifies cs`ready;
    modifies cs.stream_manager`segment_nodes_repr, cs`epoch, cs`cstate, cs`mitls_reader_key, cs`mitls_writer_key;
    modifies cs.stream_manager.segment_nodes_repr, cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr;

    modifies cs.stream_manager.ready_streams, cs.stream_manager.ready_streams.Repr;

    // modifies cs.keys;
    modifies cs.pspace_manager`crypto_states;
    modifies cs.pspace_manager`crypto_states_repr;
    modifies cs.pspace_manager.ps_states_repr;
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));

    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.ready_streams.Repr - old(cs.stream_manager.ready_streams.Repr));
    ensures cs.Valid();
    ensures buffer_offset_valid_pos(packet_len, offset, x);

{
    print("DEBUG DFY] decoding crypto frame ", ps_str(ps), "\n");

    var temp_0 := decode_CRYPTO_frame(packet, packet_len, offset);
    if temp_0.Fail? { return Fail(temp_0.err);}
    var segment, offset := temp_0.value.0, temp_0.value.1;

    var segment_ := cs.stream_manager.add_partial_receive_data_to_crypto_stream(ps, segment);

    if segment_.None? {
        print("DEBUG DFY] no new crypto frame\n");
        return Ok(offset);
    }

    segment := segment_.value;
    // if data is ready, process immediately
    var _ := process_crypto_segment(cs, segment);
    quic_stream_mutable.deleteSegment(segment);

    return Ok(offset);
}

method decode_STREAM_frame (packet:buffer_t, packet_len:uint32, offset:uint32, frame_type:uint8)
    returns (x:Err<(uint32, uint62, qstream_segment_fixed)>)
    requires buffer_offset_valid_pre(packet, packet_len, offset);
    ensures x.Ok? ==> offset < x.value.0 <= packet_len;  // can be equal
{
    var fin := and8(frame_type, 1);
    var len := and8(frame_type / 2, 1);
    var off := and8(frame_type / 4, 1);

    var temp_0 := decode_variable_loose(packet, packet_len, offset);
    if temp_0.Fail? { return Fail("unable to decode stream id"); }

    var stream_id, stream_offset, data_length, offset;

    stream_id, offset := temp_0.value.0, temp_0.value.1;

    stream_offset := 0;

    if off != 0 {
        var temp_1 := decode_variable_loose(packet, packet_len, offset);
        if temp_1.Fail? { return Fail("unable to decode stream offset"); }
        stream_offset, offset := temp_1.value.0, temp_1.value.1;
    }

    if len == 0 {
        if packet_len <= offset { return Fail("invalid data length"); }
        data_length := packet_len - offset; // Stream Data field extends to the end of the packet.
    } else {
        var temp_2 := decode_variable_loose(packet, packet_len, offset);
        if temp_2.Fail? { return Fail("unable to decode stream offset"); }
        if temp_2.value.0 > UINT32_MAX as uint62 { return Fail("invalid data length"); }
        data_length, offset := temp_2.value.0 as uint32, temp_2.value.1;
    }

    if data_length > packet_len - offset { return Fail("Stream data length too long"); }

    if stream_offset as uint64 + data_length as uint64 > UINT62_MAX {
        return Fail("segment_offset makes no sense");
    }

    var segment : qstream_segment_fixed := qstream_segment_raw(
        stream_offset,
        packet[offset..offset+data_length],
        data_length,
        if fin == 1 then true else false,
        true,
        0,
        stream_id
    );

    offset := offset + data_length;
    return Ok((offset, stream_id, segment));
}

method process_STREAM_frame (cs:connection, packet:buffer_t, packet_len:uint32, offset:uint32, frame_type:uint8)
  returns (x:Err<uint32>)

  requires buffer_offset_valid_pre(packet, packet_len, offset);
  requires cs.Valid();

  modifies cs`ready;
  // modifies cs.keys;
    modifies cs.pspace_manager`crypto_states;
    modifies cs.pspace_manager`crypto_states_repr;
    modifies cs.pspace_manager.ps_states_repr;
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
  modifies cs`epoch, cs`cstate, cs`mitls_reader_key, cs`mitls_writer_key;

  modifies cs.stream_manager.segment_nodes_repr,
    cs.stream_manager.segment_lists_repr,
    cs.stream_manager.quic_streams_repr;

  modifies cs.stream_manager`peer_streams_bidi,
    cs.stream_manager`peer_streams_uni,
    cs.stream_manager`segment_nodes_repr,
    cs.stream_manager`segment_lists_repr,
    cs.stream_manager`quic_streams_repr;

    modifies cs.stream_manager.stream_lists_repr,
        cs.stream_manager.stream_nodes_repr;
    modifies cs.stream_manager`stream_nodes_repr;

  ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr));
  ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
  ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr));
  ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));

  ensures cs.Valid();
  ensures buffer_offset_valid_pos(packet_len, offset, x);

{
    var temp_0 := decode_STREAM_frame(packet, packet_len, offset, frame_type);
    if temp_0.Fail? { return Fail(temp_0.err); }
    var offset, stream_id, segment := temp_0.value.0, temp_0.value.1, temp_0.value.2;
    var _ := cs.receive_stream_frame(stream_id, segment);
    return Ok(offset);
}

// Parse MaxData
method process_MAX_DATA_frame (cs:connection, packet:buffer_t, packet_len:uint32, offset:uint32) returns (x:Err<uint32>)

  requires buffer_offset_valid_pre(packet, packet_len, offset);
  requires cs.Valid();
  modifies cs`ready;
  modifies cs.stream_manager`peer_max_data;
  ensures cs.Valid();
  ensures buffer_offset_valid_pos(packet_len, offset, x);

{
    var temp_0 := decode_variable_loose(packet, packet_len, offset );
    if temp_0.Fail? { return Fail("failed to deocde max_data"); }
    var max_data, offset := temp_0.value.0, temp_0.value.1;

    if cs.stream_manager.peer_max_data < max_data {
        cs.stream_manager.peer_max_data := max_data;
        cs.update_send_data_ready(); //  (* Now that data can be sent, try sending data *)
    }
    return Ok(offset);
}

method decode_MAX_STREAM_DATA_frame(packet:buffer_t, packet_len:uint32, offset:uint32)
    returns (x: Err<(uint62, uint62, uint32)>)
    requires buffer_offset_valid_pre(packet, packet_len, offset);
    ensures x.Ok? ==> offset < x.value.2 <= packet_len;
{
    var temp_0 := decode_variable_loose(packet, packet_len, offset);
    if temp_0.Fail? { return Fail("unable to decode stream_id"); }
    var stream_id, max_stream_data, offset;
    stream_id, offset := temp_0.value.0, temp_0.value.1;

    var temp_1 := decode_variable_loose(packet, packet_len, offset );
    if temp_1.Fail? { return Fail("unable to decode max_stream_data"); }
    max_stream_data, offset := temp_1.value.0, temp_1.value.1;
    return Ok((stream_id, max_stream_data, offset));
}

// Parse MaxStreamData
method process_MAX_STREAM_DATA_frame (cs:connection, packet:buffer_t, packet_len:uint32, offset:uint32)
    returns (x :Err<uint32>)

    requires buffer_offset_valid_pre(packet, packet_len, offset);
    requires cs.Valid();

    modifies cs.stream_manager`peer_streams_bidi,
        cs.stream_manager`peer_streams_uni;

    modifies cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`segment_lists_repr,
        cs.stream_manager`quic_streams_repr;

    modifies cs.stream_manager.quic_streams_repr;
    modifies cs.stream_manager.stream_lists_repr,
        cs.stream_manager.stream_nodes_repr;
    modifies cs.stream_manager`stream_nodes_repr;

    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))
    ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr))
    ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr))
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr))

    ensures cs.Valid();
    ensures buffer_offset_valid_pos(packet_len, offset, x);
{
    var temp := decode_MAX_STREAM_DATA_frame(packet, packet_len, offset);
    if temp.Fail? { return Fail("failed to decode MAX_STREAM_DATA"); }
    var stream_id, max_stream_data, offset := temp.value.0, temp.value.1, temp.value.2;
    cs.stream_manager.set_max_stream_data(stream_id, max_stream_data);
    return Ok(offset);
}

method process_MAX_STREAMS_frames (cs:connection, packet:buffer_t, packet_len:uint32, offset:uint32, frame_type:uint8)
    returns (x:Err<uint32>)

    requires buffer_offset_valid_pre(packet, packet_len, offset);
    requires cs.Valid();
    modifies cs.stream_manager`peer_max_streams_bidi,
        cs.stream_manager`peer_max_streams_uni;
    ensures cs.Valid();
    ensures buffer_offset_valid_pos(packet_len, offset, x);
{
    var temp_0 := decode_variable_loose(packet, packet_len, offset);
    if temp_0.Fail? { return Fail(temp_0.err); }
    var max_streams, offset := temp_0.value.0, temp_0.value.1;

    if frame_type == MAX_STREAMS_BIDI_TYPE { // MAX BIDI stream ID
        if cs.stream_manager.peer_max_streams_bidi < max_streams {
            cs.stream_manager.peer_max_streams_bidi := max_streams;
        }
     } else if frame_type == MAX_STREAMS_UNI_TYPE { // MAX UNI stream ID
        if cs.stream_manager.peer_max_streams_uni < max_streams {
            cs.stream_manager.peer_max_streams_uni := max_streams;
        }
    } else {
        return Fail("wrong frame type byte");
    }
    return Ok(offset);
}

// (** Parse CONNECTION_CLOSE *)
method process_CONNECTION_CLOSE_frame (cs:connection, packet:buffer_t, packet_len:uint32, offset:uint32, frame_type:uint8)
    returns (x:Err<uint32>)
    requires cs.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, offset);
    modifies cs`cstate;
    ensures cs.Valid();
    ensures buffer_offset_valid_pos(packet_len, offset, x);
{
    var temp := decode_variable_loose(packet, packet_len, offset);
    if temp.Fail? { return Fail("cannot decode err_ocode"); }
    var err_ocode, err_frame_type, reason_phrase_length, offset;
    err_ocode, offset := temp.value.0, temp.value.1;

    if frame_type == CONNECTION_CLOSE_QUIC_TYPE {
        temp := decode_variable_loose(packet, packet_len, offset);
        if temp.Fail? { return Fail("cannot decode frame type"); }
        err_frame_type, offset := temp.value.0, temp.value.1;
    }

    temp := decode_variable_loose(packet, packet_len, offset);
    if temp.Fail? { return Fail("cannot decode reason_phrase_length"); }
    if temp.value.0 > UINT32_MAX as uint62 { return Fail("invalid Reason Phrase Length"); }
    reason_phrase_length, offset := temp.value.0 as uint32, temp.value.1;

    if reason_phrase_length > packet_len - offset {
        x := Fail("CONNECTION_CLOSE with invalid Reason Phrase Length");
    } else {
        offset := offset + reason_phrase_length;
        cs.cstate :=  Closed;
        x := Ok(offset);
    }
    cancel_timer(cs.lrcc_manager.ping_alarm);
}

// Parse a protected frame of data
method {:timeLimit 60} process_short_header_frame (cs:connection, packet:buffer_t, packet_len:uint32, offset:uint32)
    returns (x:Err<process_result>)

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
    
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
    ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr))

    ensures cs.Valid();
    ensures buffer_offset_valid_pos2(packet_len, offset, x);
{
    var temp := getu8_s(packet, packet_len, offset );
    if temp.Fail? { return Fail("cannot read frame type"); }
    var frame_type := temp.value; // Frame Type
    var offset := offset + 1;

    // handle the frames that does not have payload first
    if frame_type == PADDING_TYPE {
        return Ok(process_result(offset, false));
    } else if frame_type == PING_TYPE {
        fatal("NYI");
    }

    if offset == packet_len { return Fail("cannot read frame data"); }

    // the rest of the frames should all have payload, move up  if necessary

    var offset_op := Fail("unimplemented");
    var ack_eliciting := true;

    if frame_type == ACK_NON_ECN_TYPE
        || frame_type == ACK_ECN_TYPE {
        offset_op := process_ACK_frame(cs, APPLICATION_SPACE, packet, packet_len, offset, frame_type);
        ack_eliciting := false;
    } else if frame_type == RESET_STREAM_TYPE {
        offset_op := process_RESET_STREAM_frame(cs, packet, packet_len, offset);
    } else if STREAM_TYPE_LOWER <= frame_type <= STREAM_TYPE_UPPER {
        offset_op := process_STREAM_frame(cs, packet, packet_len, offset, frame_type);
    } else if frame_type == MAX_DATA_TYPE {
        offset_op := process_MAX_DATA_frame(cs, packet, packet_len, offset);
    } else if frame_type == MAX_STREAM_DATA_TYPE {
        offset_op := process_MAX_STREAM_DATA_frame(cs, packet, packet_len, offset);
    } else if frame_type == MAX_STREAMS_BIDI_TYPE
        || frame_type == MAX_STREAMS_UNI_TYPE {
        offset_op := process_MAX_STREAMS_frames(cs, packet, packet_len, offset, frame_type);
    } else if frame_type == CONNECTION_CLOSE_QUIC_TYPE
        || frame_type == CONNECTION_CLOSE_APP_TYPE {
        offset_op := process_CONNECTION_CLOSE_frame(cs, packet, packet_len, offset, frame_type);
    } else if frame_type == CRYPTO_TYPE {
        offset_op := process_CRYPTO_frame(cs, APPLICATION_SPACE, packet, packet_len, offset);
    } else if frame_type == DATA_BLOCKED_TYPE {
        fatal("NYI");
    } else if frame_type == STREAM_DATA_BLOCKED_TYPE {
        fatal("NYI");
    } else if frame_type == STREAMS_BLOCKED_BIDI_TYPE
        || frame_type == STREAMS_BLOCKED_UNI_TYPE {
        fatal("NYI");
    } else if frame_type == NEW_CONNECTION_ID_TYPE {
        fatal("NYI");
    } else if frame_type == RETIRE_CONNECTION_ID_TYPE {
        fatal("NYI");        
    } else if frame_type == PATH_CHALLENGE_TYPE {
        fatal("NYI");
    } else if frame_type == PATH_RESPONSE_TYPE {
        fatal("NYI");
    } else if frame_type == STOP_SENDING_TYPE {
        fatal("NYI");
    } else if frame_type == NEW_TOKEN_TYPE {
        fatal("NYI");
    }  else {
        offset_op := Fail("invalid frame encoding");
    }

    if offset_op.Fail? {
        return Fail(offset_op.err);
    }
    return Ok(process_result(offset_op.value, ack_eliciting));
}

method process_short_header_frames (cs:connection, packet:buffer_t, packet_len:uint32, offset:uint32)
    returns (x:Err<process_result>)

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
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager.ps_states_repr, 
        cs.pspace_manager.ack_buffers_repr,
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
    
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
    ensures fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr))

    ensures cs.Valid();
    ensures buffer_offset_valid_pos2(packet_len, offset, x);
{
    var cur_offset := offset;
    var ack_eliciting := false;

    while cur_offset < packet_len
        invariant cs.Valid();
        invariant buffer_offset_valid_pre(packet, packet_len, cur_offset);
        invariant cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
        invariant fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr))
        invariant fresh(cs.stream_manager.segment_lists_repr - old(cs.stream_manager.segment_lists_repr))
        invariant fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))
        invariant fresh(cs.stream_manager.quic_streams_repr - old(cs.stream_manager.quic_streams_repr))
        invariant fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
        invariant fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr))
    {
        var temp := process_short_header_frame(cs, packet, packet_len, cur_offset);
        if temp.Fail? { return Fail(temp.err); }
        var frame_result := temp.value;

        if frame_result.ack_eliciting {
            ack_eliciting := true;
        }

        if frame_result.offset == packet_len {
            return Ok(process_result(packet_len, ack_eliciting));
        }
        cur_offset := frame_result.offset;
    }

    return Ok(process_result(cur_offset, ack_eliciting));
}

/*
    The payload of an Initial packet includes a CRYPTO frame (or frames) containing a cryptographic handshake message, ACK frames, or both. PADDING and CONNECTION_CLOSE frames are also permitted. An endpoint that receives an Initial packet containing other frames can either discard the packet as spurious or treat it as a connection error.

    The payload of this packet contains CRYPTO frames and could contain PADDING, or ACK frames. Handshake packets MAY contain CONNECTION_CLOSE frames. Endpoints MUST treat receipt of Handshake packets with other frames as a connection error.
*/

method process_handshake_or_initial_frame (
        cs:connection,
        ps: packet_space,
        packet:buffer_t,
        packet_len:uint32,
        offset:uint32)
    returns (x: Err<process_result>)

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

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    ensures cs.Valid();
    ensures buffer_offset_valid_pos2(packet_len, offset, x);

{
    var temp := getu8_s(packet, packet_len, offset );
    if temp.Fail? { return Fail("cannot read frame type"); }
    var frame_type := temp.value; // Frame Type
    var offset := offset + 1;

    if frame_type == PADDING_TYPE {
        return Ok( process_result(offset, false));
    }

    if offset == packet_len { return Fail("cannot read frame data"); }
    var ack_eliciting := false;
    var offset_;

    if frame_type == CRYPTO_TYPE {
        offset_ := process_CRYPTO_frame(cs, ps, packet, packet_len, offset);
        ack_eliciting := true;
    } else if frame_type == ACK_NON_ECN_TYPE
        || frame_type == ACK_ECN_TYPE {
        offset_ := process_ACK_frame(cs, ps, packet, packet_len, offset, frame_type);
    } else if frame_type == CONNECTION_CLOSE_APP_TYPE
        || frame_type == CONNECTION_CLOSE_QUIC_TYPE {
        offset_ := process_CONNECTION_CLOSE_frame(cs, packet, packet_len, offset, frame_type);
    } else {
        print("[DEBUG DFY] unsupported cleartext frame type ", frame_type, "\n");
        offset_ := Fail("Invalid frame type");
    }
    if offset_.Fail? { return Fail(offset_.err); }
    return Ok(process_result(offset_.value, ack_eliciting));
}

// Parse all of the frames within an initial or handshake packet
method process_handshake_or_initial_frames(cs:connection, ps: packet_space, packet:buffer_t, packet_len:uint32, offset:uint32)
    returns (x:Err<process_result>)

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
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr,
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

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
    
    ensures cs.Valid();
    ensures buffer_offset_valid_pos2(packet_len, offset, x);
{
    var cur_offset : uint32 := offset;
    var ack_eliciting := false;

    while cur_offset < packet_len
        invariant cs.Valid();
        invariant buffer_offset_valid_pre(packet, packet_len, cur_offset);
        invariant cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
        invariant fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
        invariant fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));
        invariant fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));
        invariant fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    {
        var result_ := process_handshake_or_initial_frame(cs, ps, packet, packet_len, cur_offset);
        if result_.Fail? { return Fail(result_.err); }
        var result := result_.value;

        if result.ack_eliciting {
            ack_eliciting := true;
        }
        // needs early return before assignment
        if result.offset == packet_len {
            return Ok(process_result(result.offset, ack_eliciting));
        }
        cur_offset := result.offset;
    }

    return Ok(process_result(cur_offset, ack_eliciting));
}

method decode_client_initial_crypto_frame(packet:buffer_t, packet_len:uint32, offset:uint32)
    returns (x :Err <(qstream_segment_fixed, uint32)>)
    requires buffer_offset_valid_pre(packet, packet_len, offset);
{
    var temp_0 := getu8_s(packet, packet_len, offset);
    if temp_0.Fail? { return Fail("cannot read frame type"); }
    var frame_type := temp_0.value; // Frame Type

    // The first CRYPTO frame sent always begins at an offset of 0
    if frame_type != CRYPTO_TYPE {
        return Fail("First frame must be a CRYPTO frame");
    }
    
    if offset >= packet_len - 1 {
        return Fail("insufficient buffer");
    }

    x := decode_CRYPTO_frame(packet, packet_len, offset + 1);
}

method process_client_initial_crypto_frame(cs: connection, packet:buffer_t, packet_len:uint32, offset: uint32)
    returns (x: Err<uint32>)

    requires cs.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, offset);

    modifies cs.stream_manager`segment_nodes_repr;
    modifies cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr;
    modifies cs`epoch, cs`cstate, cs`mitls_reader_key, cs`mitls_writer_key, cs`ready;
    // modifies cs.keys;
    modifies cs.pspace_manager`crypto_states;
    modifies cs.pspace_manager`crypto_states_repr;
    modifies cs.pspace_manager.ps_states_repr;
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));

    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures cs.Valid();
{
    var temp_0 := decode_client_initial_crypto_frame(packet, packet_len, offset);
    if temp_0.Fail? { 
        print("[DEBUG DFY] failed to decode client initial crypto frame\n");
        return Fail("failed to decode client initial crypto frame");
    }
    var segment, offset := temp_0.value.0, temp_0.value.1;
    cs.stream_manager.set_initial_crypto_stream_offset(segment.datalength as uint62);

    var _ := process_crypto_segment(cs, segment);
    return Ok(offset);
}

// (** Parse all frames within a ClientHello send to a server *)
method process_client_initial_frames(cs: connection, packet:buffer_t, packet_len:uint32, start_offset:uint32)
    returns (x:Err<uint32>)

    requires cs.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, start_offset);

    modifies cs`ready, cs`epoch, cs`cstate, cs`mitls_reader_key, cs`mitls_writer_key;

    modifies cs.fixedframes, cs.fixedframes.buffer;

    modifies cs.lrcc_manager`largest_acked_packet,
        cs.lrcc_manager`latest_rtt,
        cs.lrcc_manager`min_rtt,
        cs.lrcc_manager`rttvar,
        cs.lrcc_manager`smoothed_rtt,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time,
        cs.lrcc_manager`loss_time,
        cs.lrcc_manager.sent_packets,
        cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager`crypto_states,
        cs.pspace_manager`crypto_states_repr,
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

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    ensures cs.Valid();
{
    var temp := process_client_initial_crypto_frame(cs, packet, packet_len, start_offset);
    if temp.Fail? { return Fail(temp.err); }
    var offset := temp.value;

    if offset >= packet_len { return Ok(offset); } // no more to be read
    var processed := process_handshake_or_initial_frames(cs, INITIAL_SPACE, packet, packet_len, offset);
    if processed.Fail? { return Fail(processed.err); }
    x := Ok(processed.value.offset); 
}

method is_connection_close_frame(frame:fixed_frame_fixed) returns (x:bool)
{
    var framedata := frame.framedata;
    var frame_length := frame.framelength;

    if frame_length == 0 { return false; }
    var frame_type := framedata[0];

    if frame_type == CONNECTION_CLOSE_QUIC_TYPE
        || frame_type == CONNECTION_CLOSE_APP_TYPE {
        return true;
    }
    return false;
}

// (** Prepare a fixed frame *)
method prepare_fixed_frame (
    packet:buffer_t,
    packet_len:uint32,
    p:uint32,
    frame:fixed_frame_fixed)
    returns (x : Err<uint32>)

    requires buffer_offset_valid_pre(packet, packet_len, p);

    modifies packet;

    ensures x.Ok? ==> x.value as int == p as int + frame.framelength as int
        && buffer_offset_valid_pos(packet_len, p, x);
{
    var framedata := frame.framedata;
    var frame_length := frame.framelength;

    if frame_length == 0 { return Fail("[ERROR] invalid fixed frame"); }
    var frame_type := framedata[0];

    if frame_type == PADDING_TYPE { print("[DEBUG DFY] PADDING fixed frame"); }
    else if frame_type == RESET_STREAM_TYPE { print("[DEBUG DFY] RESET_STREAM fixed frame"); }
    else if frame_type == STOP_SENDING_TYPE { print("[DEBUG DFY] STOP_SENDING fixed frame"); }
    else if frame_type == NEW_TOKEN_TYPE { print("[DEBUG DFY] NEW_TOKEN fixed frame"); }
    else if frame_type == MAX_DATA_TYPE { print("[DEBUG DFY] MAX_DATA fixed frame"); }
    else if frame_type == MAX_STREAM_DATA_TYPE { print("[DEBUG DFY] MAX_STREAM_DATA fixed frame"); }
    else if frame_type == MAX_STREAMS_BIDI_TYPE { print("[DEBUG DFY] MAX_STREAMS_BIDI fixed frame"); }
    else if frame_type == MAX_STREAMS_UNI_TYPE { print("[DEBUG DFY] MAX_STREAMS_UNI fixed frame"); }
    else if frame_type == DATA_BLOCKED_TYPE { print("[DEBUG DFY] DATA_BLOCKED fixed frame"); }
    else if frame_type == STREAM_DATA_BLOCKED_TYPE { print("[DEBUG DFY] STREAM_DATA_BLOCKED fixed frame"); }
    else if frame_type == STREAMS_BLOCKED_BIDI_TYPE { print("[DEBUG DFY] STREAMS_BLOCKED_BIDI fixed frame"); }
    else if frame_type == STREAMS_BLOCKED_UNI_TYPE { print("[DEBUG DFY] STREAMS_BLOCKED_UNI fixed frame"); }
    else if frame_type == NEW_CONNECTION_ID_TYPE { print("[DEBUG DFY] NEW_CONNECTION_ID fixed frame"); }
    else if frame_type == RETIRE_CONNECTION_ID_TYPE { print("[DEBUG DFY] RETIRE_CONNECTION_ID fixed frame"); }
    else if frame_type == PATH_CHALLENGE_TYPE { print("[DEBUG DFY] PATH_CHALLENGE fixed frame"); }
    else if frame_type == PATH_RESPONSE_TYPE { print("[DEBUG DFY] PATH_RESPONSE fixed frame"); }
    else if frame_type == CONNECTION_CLOSE_QUIC_TYPE { print("[DEBUG DFY] CONNECTION_CLOSE_QUIC fixed frame"); }
    else if frame_type == CONNECTION_CLOSE_APP_TYPE { print("[DEBUG DFY] CONNECTION_CLOSE_APP fixed frame"); }
    else { return Fail("[DEBUG DFY] Unknown fixed frame"); }

    if packet_len - p < frame_length { return Fail("[ERROR] not enough space to encode fixed frame");}

    var p := append_sequence(packet, p, framedata, frame_length);

    return Ok(p);
}

}
