include "Options.dfy"
include "NativeTypes.dfy"
include "PrivateDLL.dfy"
include "DynamicArray.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "HandleFFIs.dfy"
include "QStream.dfy"
include "QStreamManager.dfy"
include "QLossRecovery.dfy"
include "QPacketSpace.dfy"
include "Extern.dfy"
include "QUICUtils.dfy"

module QConnection {

import opened Options
import opened NativeTypes
import opened PrivateDLL
import opened DynamicArray
import opened QUICDataTypes
import opened QUICConstants
import opened HandleFFIs
import opened QStream
import opened QStreamManager
import opened QLossRecovery
import opened QPacketSpace
import opened Extern
import opened QUICUtils


datatype epoch =
    | EpochInitial
    | Epoch0RTT
    | EpochHandshake
    | Epoch1RTT

datatype connection_fixed = connection_fixed( // ()
    monitor: voidptr,
    is_client:bool,
    hostname:seq<char>,

    statelessResetToken: reset_token_t,
    handshakeComplete: handle_t // A HANDLE to an auto reset event
)

type packet_holder_vector = Vector<packet_holder_fixed>
type fixed_frame_vector = Vector<fixed_frame_fixed>

// All state associated with a QUIC connection between two computers
class connection {
    var ready : bool;
    var cstate: connection_state;
    var closedReason: seq<char>; // set whenever the connection is closed
    var app_state: voidptr; // opaque-to-QUICFStar app state associated with the connection

    var src_connection_id: connection_id_fixed;
    var dst_connection_id: connection_id_fixed;

    var mitls_state: quic_state;
    var epoch: epoch;
    var mitls_reader_key: int32;
    var mitls_writer_key: int32;

    /* peer parameters and related state variables */
    var peer_max_packet_size: uint32; // the max size of packets that peer is willing to receive

    var pingPending : bool;
    var tls_ticket: Pointer<mitls_ticket>; // 0-RTT support

    var short_header_packets: packet_holder_vector;
    var fixedframes: fixed_frame_vector;
    var cf_state: connection_fixed;
    var lrcc_manager: LRCCManager;

    var stream_manager : StreamManager;
    var pspace_manager : PspaceManager;

    constructor(cf_state: connection_fixed,
        initial_keys: key_pair,
        src_connection_id: connection_id_fixed,
        dst_connection_id: connection_id_fixed)
        requires initial_keys.reader != null && initial_keys.writer != null;
        ensures this.cf_state == cf_state;
        ensures Valid()

        ensures fresh (short_header_packets)
            && fresh (short_header_packets.buffer)
            && fresh (fixedframes)
            && fresh (fixedframes.buffer)
            && fresh (lrcc_manager)
            && fresh (lrcc_manager.sent_packets)
            && fresh (lrcc_manager.sent_packets.Repr)
            && fresh (stream_manager)
            && fresh (stream_manager.quic_streams_repr)
            && fresh (stream_manager.stream_nodes_repr)
            && fresh (stream_manager.stream_lists_repr)
            && fresh (stream_manager.segment_lists_repr)
            && fresh (stream_manager.segment_nodes_repr)
            && fresh (pspace_manager)
            && fresh (pspace_manager.ps_states_repr)
            && fresh (pspace_manager.ack_buffers_repr)
            && fresh (pspace_manager.crypto_states_repr);
    {
        this.ready := false;
        this.pspace_manager := new PspaceManager();
        this.stream_manager := new StreamManager();

        this.short_header_packets := new packet_holder_vector(packet_holder_raw([1], 1));
        this.fixedframes := new fixed_frame_vector(fixed_frame_raw([], 0, 0));

        this.cf_state := cf_state;
        this.lrcc_manager := new LRCCManager(false);

        this.cstate := Start;
        this.epoch := EpochInitial;
        this.mitls_reader_key := -1;
        this.mitls_writer_key := -1;
        this.app_state := null;

        this.src_connection_id := src_connection_id;
        this.dst_connection_id := dst_connection_id;
        this.mitls_state := null;

        this.tls_ticket := null;
        this.closedReason := "";

        this.peer_max_packet_size := 1200;  // use the minimum
        this.pingPending := false;

        new;

        this.pspace_manager.update_crypto_state(INITIAL_SPACE, 0, initial_keys.reader, true);
        this.pspace_manager.update_crypto_state(INITIAL_SPACE, 0, initial_keys.writer, false);
    }

    static function method indexOfEpoch (epoch:epoch): uint32
    {
        match epoch
        case EpochInitial => epochIndexInitial as uint32
        case Epoch0RTT => epochIndex0RTT as uint32
        case EpochHandshake => epochIndexHandshake as uint32
        case Epoch1RTT => epochIndex1RTT as uint32
    }

    static method epoch_to_packet_space(epoch:epoch) returns (x : packet_space)
    {
        match epoch
            case EpochInitial => x := INITIAL_SPACE;
            case Epoch0RTT => fatal("0RTT unsupported");
            case EpochHandshake =>  x := HANDSHAKE_SPACE;
            case Epoch1RTT =>  x := APPLICATION_SPACE;
    }

    predicate Valid()
        reads this;
        reads short_header_packets, // UNIQUE: Vector<packet_holder_fixed>
            short_header_packets.buffer; // UNIQUE: array<packet_holder_fixed>
        reads fixedframes, //  UNIQUE: Vector<fixed_frame_fixed>
            fixedframes.buffer; // UNIQUE: array<fixed_frame_fixed>
        reads lrcc_manager, // UNIQUE: LRCCManager
            lrcc_manager.sent_packets, // UNIQUE: PrivateDoublyLinkedList<sent_packet_fixed>
            lrcc_manager.sent_packets.Repr;  // UNIQUE: set<PrivateNode<sent_packet_fixed>>
        reads stream_manager, // UNIQUE:StreamManager
            stream_manager.quic_streams_repr, // UNIQUE: set<quic_stream_mutable>
            stream_manager.stream_nodes_repr, // UNIQUE: set<PrivateNode<quic_stream_mutable>>
            stream_manager.stream_lists_repr, // UNIQUE: set<PrivateDoublyLinkedList<quic_stream_mutable>>
            stream_manager.segment_lists_repr, // UNIQUE: set<PrivateDoublyLinkedList<qstream_segment_fixed>>
            stream_manager.segment_nodes_repr; // UNIQUE: set<PrivateNode<qstream_segment_fixed>>
        reads pspace_manager, // UNIQUE: PspaceManager
            pspace_manager.ps_states_repr, // UNIQUE: set<packet_space_state>
            pspace_manager.ack_buffers_repr; // UNIQUE: set<buffer<packet_num_t>>
    {
        && short_header_packets.Valid()
        && fixedframes.Valid()
        && lrcc_manager.Valid()
        && stream_manager.Valid()
        && pspace_manager.Valid()
    }

    method enqueue_fixed_frame(frame: fixed_frame_fixed) returns (handle: handle_t)
        requires Valid();
        modifies fixedframes, fixedframes.buffer;
        ensures fixedframes.buffer == old(fixedframes.buffer) || fresh(fixedframes.buffer);
        ensures Valid();
    {
        fixedframes.push_back(frame);
        handle := frame.handle;
    }

    method packet_space_send_data_pending(ps: packet_space) returns (x: bool)
        requires Valid();
    {
        var pss := pspace_manager.get_packet_space_state(ps);
        var ack_pending := pss.outgoing_ack_pending();
        
        var stream := stream_manager.get_crypto_stream(ps);
        var data_pending := stream.has_send_data_pending();
        return data_pending || ack_pending;
    }

    method connection_send_data_pending () returns (x: Option<packet_space>)
        requires Valid();
    {
        // Prioritize pending data from lower numbered epochs
        var epochIndex := indexOfEpoch(epoch) as byte;

        if cstate != Running {
          print("[DEBUG DFY] connection_send_data_pending : cstate != Running\n");
          return None;
        }

        if epochIndex < epochIndexInitial {
          print("[DEBUG DFY] connection_send_data_pending : epochIndex < epochIndexInitial\n");
          return None;
        }
        var data_pending := packet_space_send_data_pending(INITIAL_SPACE);
        if data_pending { return Some(INITIAL_SPACE); }

        if epochIndex < epochIndexHandshake { return None; }
        data_pending := packet_space_send_data_pending(HANDSHAKE_SPACE);
        if data_pending { return Some(HANDSHAKE_SPACE); }

        if epochIndex != epochIndex1RTT { return None; }
        data_pending := packet_space_send_data_pending(APPLICATION_SPACE);
        if data_pending { return Some(APPLICATION_SPACE); }

        var reay_stream := stream_manager.find_send_ready_stream();

        if pingPending || fixedframes.current_size != 0 || reay_stream != null {
            return Some(APPLICATION_SPACE);
        }

        return None;
    }

    method update_epoch(bReadKeyChanged: bool) returns (new_epoch: epoch)
        requires Valid();
        modifies this`epoch;
        ensures Valid();
    {
        if epoch == EpochInitial {
            new_epoch :=
                if  cf_state.is_client then EpochHandshake
                //  Client, but no RTT inside QUIC_handshake()
                else if bReadKeyChanged then Epoch0RTT
                // Initial, and read key changed... 0-RTT is supported
                else EpochHandshake; // Initial, and read key didn't change.  No 0-RTT
        } else if epoch == Epoch0RTT {
            new_epoch := EpochHandshake;
        } else if epoch == EpochHandshake {
            new_epoch := Epoch1RTT;
        } else if epoch == Epoch1RTT {
            new_epoch := Epoch1RTT;
        }

        epoch := new_epoch;
    }

    method enter_monitor()
        requires Valid();
        ensures Valid();
    {
        monitor_enter(cf_state.monitor);
    }

    method exit_monitor()
        requires Valid();
        ensures Valid();
    {
        monitor_exit(cf_state.monitor);
    }

    method update_dcid(cid: connection_id_fixed)
        requires Valid();
        modifies this`dst_connection_id;
        ensures Valid();
    {
        if cf_state.is_client {
            print("[DEBUG DFY] client dcid updated\n");
            var temp := build_buffer_from_seq(cid.cid, cid.len as uint32);
            dump_buffer(temp, 0, cid.len as uint32);
            dst_connection_id := cid;
        }
    }

    // Refresh the 'ready to send' state for the connection
    method update_send_data_ready ()
        requires Valid();
        modifies this`ready;
        ensures Valid();
    {
        var packetSpace := connection_send_data_pending();
        var under_limit := lrcc_manager.under_cc_limit();
        if packetSpace != None && under_limit {
            ready := true;
            set_event_handle(engine_send_data_ready());
        }
    }

    // Send data on a stream, without blocking until the data is actually sent.  Returns a waitable HANDLE.
    method send_stream_data_async(stream: quic_stream_mutable, data:buffer_t, data_len: uint32, fin:bool) returns (x:handle_t)
        requires Valid();
        requires data != null && data.Length == data_len as int;
        requires stream_manager.stream_in_manager(stream);

        modifies this`ready;

        modifies stream_manager`segment_nodes_repr;
        modifies stream_manager.quic_streams_repr,
            stream_manager.segment_nodes_repr,
            stream_manager.segment_lists_repr;

        ensures fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));
        ensures Valid();
    {
        enter_monitor();
        var _ := send_stream_data_async_locked(stream, data, data_len, fin);
        exit_monitor();
    }

    // call this version when locked 
    method send_stream_data_async_locked(stream: quic_stream_mutable, data:buffer_t, data_len: uint32, fin:bool)
        returns (x:handle_t)

        requires Valid();
        requires data != null && data.Length == data_len as int;
        requires stream_manager.stream_in_manager(stream);

        modifies this`ready;

        modifies stream_manager`segment_nodes_repr;
        modifies stream_manager.quic_streams_repr,
            stream_manager.segment_nodes_repr,
            stream_manager.segment_lists_repr;

        ensures fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));
        ensures Valid();
    {
        x := stream_manager.add_send_data_to_stream_impl(stream, data, data_len, fin);
        assert Valid();
        update_send_data_ready();
    }

    method send_crypto_frame(outbuf: buffer<byte>, output_len: uint32)
        requires Valid();
        requires outbuf != null && outbuf.Length == output_len as int;

        modifies this`ready;
        modifies stream_manager`segment_nodes_repr;
        modifies stream_manager.quic_streams_repr,
            stream_manager.segment_nodes_repr,
            stream_manager.segment_lists_repr;

        ensures fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));
        ensures Valid();
    {
        // Send the data in the current packet space, before any ps/epoch update happens,
        // except when in 1RTT epoch... send using Handshake in that case.
        var epoch := if epoch == Epoch1RTT then EpochHandshake else epoch;

        var ps := epoch_to_packet_space(epoch);

        if ps == APPLICATION_SPACE {
            fatal("unsupported to send crypto frame in APPLICATION_SPACE\n");
        }

        var stream := stream_manager.get_crypto_stream(ps);

        // we have already locked the connection
        var _ := send_stream_data_async_locked(stream, outbuf, output_len, false);
    }

    // Stream data has arrived from the peer.  Merge it in, taking care of out-of-order and partial/overlapping/disjoint segments
    method receive_stream_frame (id:uint62, segment:qstream_segment_fixed) returns (x :Err<bool>)
        requires Valid();

        modifies this`ready;
        modifies this`epoch, this`cstate, this`mitls_reader_key, this`mitls_writer_key;

        modifies stream_manager.segment_nodes_repr,
            stream_manager.segment_lists_repr,
            stream_manager.quic_streams_repr;

        modifies stream_manager`peer_streams_bidi,
            stream_manager`peer_streams_uni,
            stream_manager`segment_nodes_repr,
            stream_manager`segment_lists_repr,
            stream_manager`quic_streams_repr;

        modifies stream_manager.stream_lists_repr, stream_manager.stream_nodes_repr;
        modifies stream_manager`stream_nodes_repr;

        ensures fresh(stream_manager.quic_streams_repr - old(stream_manager.quic_streams_repr));
        ensures fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));
        ensures fresh(stream_manager.segment_lists_repr - old(stream_manager.segment_lists_repr));
        ensures fresh(stream_manager.stream_nodes_repr - old(stream_manager.stream_nodes_repr));

        ensures Valid();
    {
        if isStreamUni(id) && isStreamClientInitiated(id) == cf_state.is_client {
            return Fail("Receiving data from an unexpected uni stream direction");
        }

        stream_manager.stream_receive_impl(id, segment);
    }

    method handshake_complete_wait()
        requires Valid();
        ensures Valid();
    {
        print("[DEBUG DFY] start waiting on handshake_complete\n");
        wait_for_event_handle(cf_state.handshakeComplete, 0xffffffff);
        print("[DEBUG DFY] done waiting on handshake_complete\n");
    }

    method retransmit_frame(ps: packet_space, tracker: loss_tracker_fixed)
        requires Valid();

        modifies fixedframes, fixedframes.buffer;
        ensures fixedframes.buffer == old(fixedframes.buffer) || fresh(fixedframes.buffer);

        modifies pspace_manager.ps_states_repr,
            pspace_manager.ack_buffers_repr;

        modifies stream_manager.quic_streams_repr,
            stream_manager.segment_nodes_repr,
            stream_manager.segment_lists_repr;

        modifies stream_manager`segment_nodes_repr,
            stream_manager`total_data_sent;
        ensures fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));

        ensures Valid();
    {
        match tracker {
            case crypto_tracker(c) => stream_manager.retransmit_crypto_frame(ps, c);
            case stream_tracker(s) => stream_manager.retransmit_stream_frame(s);
            case ack_tracker(a) => pspace_manager.retransmit_ack_frame(ps, a);
            case fixed_frame_tracker(f) => var _ := enqueue_fixed_frame(f);
        }
    }

    method retransmit_packet (lost_packet:sent_packet_fixed)
        requires Valid();
    
        modifies fixedframes, fixedframes.buffer;
        ensures fixedframes.buffer == old(fixedframes.buffer) || fresh(fixedframes.buffer);

        modifies pspace_manager.ps_states_repr,
            pspace_manager.ack_buffers_repr;

        modifies stream_manager.quic_streams_repr,
            stream_manager.segment_nodes_repr,
            stream_manager.segment_lists_repr;

        modifies stream_manager`segment_nodes_repr,
            stream_manager`total_data_sent;
        ensures fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));

        ensures Valid();
    {
        var i, count := 0, lost_packet.tracker_count;
        var trackers := lost_packet.trackers;
        var pn_space := lost_packet.pn_space;

        while i < count
            invariant Valid();
            invariant fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));
            invariant fixedframes.buffer == old(fixedframes.buffer) || fresh(fixedframes.buffer);
        {
            retransmit_frame(pn_space, trackers[i]);
            i := i + 1;
        }
    }

    method retransmit_packets(loss_list: seq<sent_packet_fixed>, count:uint32)
        requires Valid();
        requires count as int == |loss_list|;

        modifies this`ready;

        modifies fixedframes, fixedframes.buffer;
        ensures fixedframes.buffer == old(fixedframes.buffer) || fresh(fixedframes.buffer);

        modifies stream_manager.quic_streams_repr,
            stream_manager.segment_nodes_repr,
            stream_manager.segment_lists_repr;

        modifies pspace_manager.ps_states_repr,
            pspace_manager.ack_buffers_repr;

        modifies stream_manager`segment_nodes_repr,
            stream_manager`total_data_sent;
        ensures fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));

        modifies lrcc_manager`bytes_in_flight;

        ensures Valid();
    {
        var i := 0;

        while i < count
            invariant Valid();
            invariant fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));
            invariant fixedframes.buffer == old(fixedframes.buffer) || fresh(fixedframes.buffer);
        {
            var unacked := loss_list[i];
            retransmit_packet(unacked);
            i := i + 1;
        }
    }

    method handle_loss_packets()
        requires Valid();

        modifies this`ready;

        modifies fixedframes, fixedframes.buffer;
        ensures fixedframes.buffer == old(fixedframes.buffer) || fresh(fixedframes.buffer);

        modifies stream_manager.quic_streams_repr,
            stream_manager.segment_nodes_repr,
            stream_manager.segment_lists_repr;

        modifies pspace_manager.ps_states_repr,
            pspace_manager.ack_buffers_repr;

        modifies stream_manager`segment_nodes_repr,
            stream_manager`total_data_sent;
        ensures fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));

        modifies lrcc_manager`bytes_in_flight,
            lrcc_manager`loss_time,
            lrcc_manager`congestion_window,
            lrcc_manager`ssthresh,
            lrcc_manager`congestion_recovery_start_time;

        modifies lrcc_manager.sent_packets,
            lrcc_manager.sent_packets.Repr;
        ensures fresh(lrcc_manager.sent_packets.Repr - old(lrcc_manager.sent_packets.Repr));

        ensures Valid();
    {
        var pair := lrcc_manager.get_loss_packets(); 
        var loss_seq, count := pair.0, pair.1;

        if count != 0 {
            retransmit_packets(loss_seq, count);
        }
    }

    method process_acked_ranges(ack_frame: ack_frame_fixed)
        returns (ack_eliciting: bool)
        requires Valid();
        modifies this`cstate;

        modifies lrcc_manager`bytes_in_flight, lrcc_manager`congestion_window;

        modifies stream_manager.quic_streams_repr,
            lrcc_manager.sent_packets,
            lrcc_manager.sent_packets.Repr;
        ensures fresh(lrcc_manager.sent_packets.Repr - old(lrcc_manager.sent_packets.Repr))
        ensures Valid();
    {
        var ranges := ack_frame.ack_blocks;
        var i := 0;

        while i < ack_frame.block_count
            invariant Valid();
            invariant fresh(lrcc_manager.sent_packets.Repr - old(lrcc_manager.sent_packets.Repr))
        {
            var block := ranges[i];
            var packet_ack_eliciting := process_acked_range(ack_frame.pn_space, block.start, block.start - block.range);
            if packet_ack_eliciting {
                ack_eliciting := true;
            }
            i := i + 1;
        }
    }

    method process_acked_range(pn_space: packet_space, hi: packet_num_t, lo: packet_num_t)
        returns (ack_eliciting: bool)

        requires Valid();
        modifies lrcc_manager`bytes_in_flight, lrcc_manager`congestion_window;
        modifies stream_manager.quic_streams_repr;
        modifies this`cstate;

        modifies lrcc_manager.sent_packets, lrcc_manager.sent_packets.Repr;
        ensures fresh(lrcc_manager.sent_packets.Repr - old(lrcc_manager.sent_packets.Repr))
        ensures Valid();
    {
        print("[DEBUG DFY] process ack range (",lo ,", " , hi, ") \n");
        var paket_number := lo;
        while paket_number <= hi // note this is inclusive
            invariant Valid();
            invariant fresh(stream_manager.quic_streams_repr - old(stream_manager.quic_streams_repr))
            invariant fresh(lrcc_manager.sent_packets.Repr - old(lrcc_manager.sent_packets.Repr))
        {
            var packet_ack_eliciting := onPacketAcked(pn_space, paket_number);
            if packet_ack_eliciting {
                ack_eliciting := true;
            }
            paket_number := paket_number + 1;
        }
    }

    // A packet has been ACK'd by the peer
    method onPacketAcked(pn_space: packet_space, acked_packet_number: packet_num_t)
        returns (ack_eliciting: bool)

        requires Valid();
        modifies lrcc_manager`bytes_in_flight, lrcc_manager`congestion_window;
        modifies stream_manager.quic_streams_repr;
        modifies this`cstate;

        modifies lrcc_manager.sent_packets, lrcc_manager.sent_packets.Repr;
        ensures fresh(lrcc_manager.sent_packets.Repr - old(lrcc_manager.sent_packets.Repr))
        ensures Valid();
    {
        var packet_op := lrcc_manager.remove_sent_packet(pn_space, acked_packet_number);
        if packet_op.Some? {
            var acked_packet := packet_op.value;
            lrcc_manager.OnPacketAckedCC(acked_packet);
            if acked_packet.ack_eliciting {
                ack_eliciting := true;
            }
            cleanup_acked_packet(acked_packet);
        }
    }

    method cleanup_acked_packet (acked_packet: sent_packet_fixed)
        requires Valid();
        modifies stream_manager.quic_streams_repr;
        modifies this`cstate;
        ensures Valid();
    {
        var i, count := 0, acked_packet.tracker_count;
        var trackers := acked_packet.trackers;

        while i < count
            invariant Valid();
        {
            match trackers[i] {
                case crypto_tracker(c) => on_crypto_frame_acked();
                case stream_tracker(s) => on_stream_frame_acked(s);
                case fixed_frame_tracker(f) => on_fixed_frame_acked(f);
                case ack_tracker(a) => on_ack_frame_acked();
            }
            i := i + 1;
        }
    }

    method on_ack_frame_acked() { }

    method on_stream_frame_acked (segment: qstream_segment_fixed)
    {
    }

    method on_crypto_frame_acked () { }

    // This handles Ack of a fixedframe
    method on_fixed_frame_acked (frame:fixed_frame_fixed)
        requires Valid();
        modifies stream_manager.quic_streams_repr;
        modifies this`cstate;
        ensures Valid();
    {
        var frame_length := frame.framelength;
        if frame_length == 0 { fatal("empty frame acked"); }

        var framedata := frame.framedata;
        var frame_type := framedata[0];

        if frame_type == PADDING_TYPE { print("[DEBUG DFY] ACKing PADDING\n"); }
        else if frame_type == STOP_SENDING_TYPE { print("[DEBUG DFY] ACKing STOP_SENDING\n"); }
        else if frame_type == NEW_TOKEN_TYPE { print("[DEBUG DFY] ACKing NEW_TOKEN\n"); }
        else if frame_type == MAX_DATA_TYPE { print("[DEBUG DFY] ACKing MAX_DATA\n"); }
        else if frame_type == MAX_STREAM_DATA_TYPE { print("[DEBUG DFY] ACKing MAX_STREAM_DATA\n"); }
        else if frame_type == MAX_STREAMS_BIDI_TYPE { print("[DEBUG DFY] ACKing MAX_STREAMS_BIDI\n"); }
        else if frame_type == MAX_STREAMS_UNI_TYPE { print("[DEBUG DFY] ACKing MAX_STREAMS_UNI\n"); }
        else if frame_type == DATA_BLOCKED_TYPE { print("[DEBUG DFY] ACKing DATA_BLOCKED\n"); }
        else if frame_type == STREAM_DATA_BLOCKED_TYPE { print("[DEBUG DFY] ACKing STREAM_DATA_BLOCKED\n"); }
        else if frame_type == STREAMS_BLOCKED_BIDI_TYPE { print("[DEBUG DFY] ACKing STREAMS_BLOCKED_BIDI\n"); }
        else if frame_type == STREAMS_BLOCKED_UNI_TYPE { print("[DEBUG DFY] ACKing STREAMS_BLOCKED_UNI\n"); }
        else if frame_type == NEW_CONNECTION_ID_TYPE { print("[DEBUG DFY] ACKing NEW_CONNECTION_ID\n"); }
        else if frame_type == RETIRE_CONNECTION_ID_TYPE { print("[DEBUG DFY] ACKing RETIRE_CONNECTION_ID\n"); }
        else if frame_type == PATH_CHALLENGE_TYPE { print("[DEBUG DFY] ACKing PATH_CHALLENGE\n"); }
        else if frame_type == PATH_RESPONSE_TYPE { print("[DEBUG DFY] ACKing PATH_RESPONSE\n"); }
        else if frame_type == CONNECTION_CLOSE_APP_TYPE { print("[DEBUG DFY] ACKing APPLICATION_CLOSE\n"); }
        else if frame_type == RESET_STREAM_TYPE {
            print("[DEBUG DFY] ACKing RST_STREAM\n");
            var data := build_buffer_from_seq(framedata, frame_length);
            var temp  := decode_variable_loose(data, frame_length, 1);
            if temp.Fail? { fatal("[ERROR DFY] unable to decode RESET_STREAM_FRAME"); }
            var stream_id := temp.value.0;
            stream_manager.on_reset_stream_acked(stream_id);
        } else if frame_type == CONNECTION_CLOSE_QUIC_TYPE {
            print("[DEBUG DFY] ACKing CONNECTION_CLOSE\n");
            cstate := Closed;
        } else {
            fatal("[ERROR DFY] unsupported fixed frame");
        }

        var handle := frame.handle;
        if handle != 0 {
            set_event_handle(handle);
        }
    }

    method process_ack_frame_impl(ack_frame: ack_frame_fixed)
        requires Valid();

        modifies this`cstate,
            this`ready;

        modifies lrcc_manager`largest_acked_packet,
            lrcc_manager`latest_rtt,
            lrcc_manager`min_rtt,
            lrcc_manager`rttvar,
            lrcc_manager`smoothed_rtt,
            lrcc_manager`bytes_in_flight,
            lrcc_manager`congestion_window,
            lrcc_manager`loss_time,
            lrcc_manager`ssthresh,
            lrcc_manager`congestion_recovery_start_time;

        modifies lrcc_manager.sent_packets, lrcc_manager.sent_packets.Repr;
        ensures fresh(lrcc_manager.sent_packets.Repr - old(lrcc_manager.sent_packets.Repr))

        modifies pspace_manager.ps_states_repr,
            pspace_manager.ack_buffers_repr;

        modifies stream_manager.quic_streams_repr,
            stream_manager.segment_nodes_repr,
            stream_manager.segment_lists_repr;

        modifies stream_manager`segment_nodes_repr,
            stream_manager`total_data_sent;
        ensures fresh(stream_manager.segment_nodes_repr - old(stream_manager.segment_nodes_repr));

        modifies fixedframes, fixedframes.buffer;
        ensures fixedframes.buffer == old(fixedframes.buffer) || fresh(fixedframes.buffer);

        ensures Valid();
    {
        var largestest_acked_pn := ack_frame.ack_blocks[0].start;
        var pn_space := ack_frame.pn_space;
        var packet_op := lrcc_manager.find_sent_packet(pn_space, largestest_acked_pn);
        var ack_eliciting := process_acked_ranges(ack_frame);

        if packet_op.Some? {
            lrcc_manager.OnAckReceived(packet_op.value, ack_eliciting, ack_frame.ack_delay);
        }

        handle_loss_packets();
    }
}
}
