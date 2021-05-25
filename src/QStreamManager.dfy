include "NativeTypes.dfy"
include "PrivateDLL.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "HandleFFIs.dfy"
include "QStream.dfy"
include "Misc.dfy"
include "Extern.dfy"
include "Options.dfy"
include "OverFlowCheck.dfy"

module QStreamManager {
import opened NativeTypes
import opened PrivateDLL
import opened QUICDataTypes
import opened QUICConstants
import opened HandleFFIs
import opened QStream
import opened Misc
import opened Extern
import opened Options
import opened OverFlowCheck

type new_stream_node = PrivateNode<quic_stream_mutable>
type new_stream_list = PrivateDoublyLinkedList<quic_stream_mutable>

class StreamManager {
    var streams : new_stream_list;
    var ready_streams : new_stream_list;

    var initial_stream: quic_stream_mutable;
    var handshake_stream: quic_stream_mutable;
    var application_stream: quic_stream_mutable;

    // // A HANDLE to a manual reset event.  Set whenever readyStreams is non-empty
    var connection_receive_data_ready: handle_t;

    ghost var segment_nodes_repr: set<segment_node>;
    ghost var segment_lists_repr: set<qstream_segment_list>;

    // this will be set(streams.Val) + {initial_stream, handshake_stream, application_stream}
    // and ready_streams.Vals should be its subset
    ghost var quic_streams_repr: set<quic_stream_mutable>;

    ghost var stream_nodes_repr : set<new_stream_node>; // this will just be streams.Repr + ready_streams.Repr
    ghost var stream_lists_repr: set<new_stream_list>; // this will just be {streams, ready_streams}

    var peer_max_stream_data_bidi_local: uint62; //  flow control limit for peer-initiated bidirectional streams
    var peer_max_stream_data_bidi_remote: uint62; //  flow control limit for local-initiated bidirectional streams
    var peer_max_stream_data_uni: uint62; // flow control limit for local-initiated uindirectional streams

    var peer_max_data: uint62; // maximum amount of data that can be sent on the connection to peer
    var total_data_sent: uint62; // sum of all data sent in STREAM frames. Must be <= peer_max_data.

    var peer_max_streams_bidi: uint62; // maximum number of bidirectional streams the peer may initiate
    var peer_streams_bidi: uint62; // number of bidirectional streams peer initiated

    var peer_max_streams_uni: uint62; // maximum number of unidirectional streams the peer may initiate
    var peer_streams_uni: uint62; // number of unidirectional streams peer initiated

    /* local parameters and related state variables */

    // var local_max_packet_size: uint32; // use default
    // var local_max_stream_data_bidi_local: uint64; // use DEFAULT_MAX_STREAM_DATA
    // var local_max_stream_data_bidi_remote: uint64; // use DEFAULT_MAX_STREAM_DATA

    var local_max_streams_bidi: uint62; // maximum number of bidirectional streams local may initiate
    var local_streams_bidi: uint62; // number of bidirectional streams local initiated

    var local_max_streams_uni: uint62; // maximum number of unidirectional streams local peer may initiate
    var local_streams_uni: uint62; // number of unidirectional streams local peer initiate

    var local_max_data: uint62; // maximum amount of data that can be received on the connection by local
    var total_data_received: uint62; // sum all all received STREAM frames. Must be <= local_max_data.

    predicate reprs_valid_bootstrap()
        reads this, stream_lists_repr;
    {
        && (ready_streams != streams)
        && stream_lists_repr == {ready_streams, streams}

        && (ready_streams.Repr !! streams.Repr)
        && stream_nodes_repr == ready_streams.Repr + streams.Repr
    }

    predicate reprs_valid()
        reads this, quic_streams_repr, stream_lists_repr;
        requires reprs_valid_bootstrap();
    {
        ghost var none_crypto_streams := (set x | x in streams.Vals);
        ghost var crypto_streams := {initial_stream, handshake_stream, application_stream};

        && (forall i, j :: 0 <= i < j < |streams.Vals| ==> (
            && (streams.Vals[i] != streams.Vals[j])))

        && (quic_streams_repr == none_crypto_streams + crypto_streams)

        && (segment_nodes_repr == flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr))
        && (segment_lists_repr == flatten_clear(set s | s in quic_streams_repr :: s.lists_repr))

        && (none_crypto_streams !! crypto_streams)
        && (forall s1, s2 :: s1 in quic_streams_repr && s2 in quic_streams_repr && s1 != s2 ==>
            (s1.nodes_repr !! s2.nodes_repr && s1.lists_repr !! s2.lists_repr))
    }

    predicate Valid()
        reads this, quic_streams_repr,
            segment_lists_repr, segment_nodes_repr,
            stream_lists_repr, stream_nodes_repr;
    {
        && reprs_valid_bootstrap()
        && reprs_valid()
        && streams.Valid()
        && ready_streams.Valid()
        && (forall rs :: rs in ready_streams.Vals ==> rs in quic_streams_repr) // subset inclusion
        && (forall s :: s in quic_streams_repr ==> s.Valid()) // each stream is valid
    }

    constructor()
        ensures Valid();
        ensures fresh (quic_streams_repr)
            && fresh (stream_nodes_repr)
            && fresh (stream_lists_repr)
            && fresh (segment_lists_repr)
            && fresh (segment_nodes_repr)
    {
        var l1 :new_stream_list := new new_stream_list();
        streams := l1;

        var l2 :new_stream_list := new new_stream_list();
        ready_streams := l2;

        var s1 := new quic_stream_mutable(0, 0xffffffff);
        var s2 := new quic_stream_mutable(0, 0xffffffff);
        var s3 := new quic_stream_mutable(0, 0xffffffff);

        initial_stream := s1;
        handshake_stream := s2;
        application_stream := s3;

        segment_nodes_repr := flatten_clear(set n | n in l1.Vals :: n.nodes_repr)
                + s1.nodes_repr + s2.nodes_repr + s3.nodes_repr;
        segment_lists_repr := flatten_clear(set n | n in l1.Vals :: n.lists_repr)
                + s1.lists_repr + s2.lists_repr + s3.lists_repr;

        quic_streams_repr := (set x | x in l1.Vals) + {s1, s2, s3};

        stream_lists_repr := {l1, l2};
        stream_nodes_repr := l1.Repr + l2.Repr;


        peer_max_stream_data_bidi_local := DEFAULT_MAX_STREAM_DATA;
        peer_max_stream_data_bidi_remote := 0;

        peer_max_data := DEFAULT_MAX_STREAM_DATA;
        total_data_sent := 0;

        peer_max_streams_bidi := 10;
        peer_streams_bidi := 0;

        peer_max_streams_uni := 0;
        peer_streams_uni := 0;

        local_max_streams_bidi := DEFAULT_MAX_STREAM_DATA;
        local_streams_bidi := 0;

        local_max_data := DEFAULT_MAX_STREAM_DATA;
        total_data_received := 0;

        var event := create_event_handle(0, 0);
        connection_receive_data_ready := event;
    }

    predicate stream_in_manager(stream: quic_stream_mutable)
        reads this, this.quic_streams_repr;
    {
        stream in quic_streams_repr
    }

    method update_connection_receive_data_ready()
        requires Valid();
        ensures Valid();
    {
        var empty := ready_streams.IsEmpty();
        if ! empty {
            print("[DEBUG DFY] setting connection receive data to ready\n");
        }
    }

    method wait_on_connection_receive_data_ready()
    {
        wait_for_event_handle(connection_receive_data_ready, 0xffffffff);
    }

    function method get_crypto_stream(ps: packet_space) : quic_stream_mutable
        reads this, quic_streams_repr,
            streams, streams.Vals, streams.Repr,
            ready_streams, ready_streams.Repr,
            segment_lists_repr, segment_nodes_repr;
        requires Valid();
        ensures get_crypto_stream(ps) in quic_streams_repr
    {
        match ps
        {
            case INITIAL_SPACE => initial_stream
            case HANDSHAKE_SPACE => handshake_stream
            case APPLICATION_SPACE => application_stream
        }
    }

    method add_new_stream(stream_id: stream_id_t, max_data:uint62) returns (new_stream: quic_stream_mutable)
        requires Valid();
        modifies this`segment_nodes_repr, this`segment_lists_repr, this`quic_streams_repr;
        modifies this.stream_lists_repr, this.stream_nodes_repr;
        modifies this`stream_nodes_repr;

        ensures Valid();
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr))
        ensures fresh(segment_lists_repr - old(segment_lists_repr))
        ensures fresh(quic_streams_repr - old(quic_streams_repr))
        ensures fresh(stream_nodes_repr - old(stream_nodes_repr))
        ensures new_stream in quic_streams_repr;
        ensures fresh(new_stream);
    {
        new_stream := new quic_stream_mutable(stream_id, max_data);

        streams.InsertTail(new_stream);

        quic_streams_repr := (set x | x in streams.Vals)
            + {initial_stream, handshake_stream, application_stream};
        segment_nodes_repr := flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr);
        segment_lists_repr := flatten_clear(set s | s in quic_streams_repr :: s.lists_repr);
        stream_nodes_repr := streams.Repr + ready_streams.Repr;
    }

    method find_stream_impl(stream_id:stream_id_t) returns (x: quic_stream_mutable?)
        requires Valid();
        ensures x != null ==> x in quic_streams_repr;
    {
        var is_empty := streams.IsEmpty();
        if  is_empty { return null; }

        var iter := new DllIterator(streams);
        var good := true;
        while good
            invariant streams.Valid();
            invariant good ==> iter.Valid();
            invariant good ==> iter.d == streams;
            decreases |streams.Vals| - iter.GetIndex(), good;
        {
            var cur :quic_stream_mutable := iter.GetVal();
            if cur.stream_id == stream_id {
                return cur;
            }
            good := iter.MoveNext();
        }
        return null;
    }

    method find_send_ready_stream() returns (stream:quic_stream_mutable?)
        requires Valid();
        ensures stream != null ==>
            (stream in quic_streams_repr && |stream.segments.Vals| != 0);
    {
        if total_data_sent >= peer_max_data {
            print("[DEBUG DFY] total_data_sent at peer_max_data limit\n");
            // Not permitted to send more stream data when the connection is at peer_max_data
            return null;
        }

        var is_empty := streams.IsEmpty();
        if  is_empty { return null; }

        var iter := new DllIterator(streams);
        var good := true;
        while good
            invariant streams.Valid();
            invariant good ==> iter.Valid();
            invariant good ==> iter.d == streams;
            decreases |streams.Vals| - iter.GetIndex(), good;
        {
            var cur :quic_stream_mutable := iter.GetVal();
            var has_pending_send_data := cur.has_send_data_pending();

            if has_pending_send_data {
                return cur;
            }
            good := iter.MoveNext();
        }

        return null;
    }

    method get_send_length(available_length: uint32) returns (x: uint32)
        requires Valid();
    {
        if peer_max_data <= total_data_sent {
            return 0; // can't send more bytes
        }
        // at most can send this many in total
        var max_allowed_length := peer_max_data as uint64 - total_data_sent as uint64;
        // can't send more than 0xffffffff in one packet
        max_allowed_length := minu64(max_allowed_length, UINT32_MAX as uint64);
        // also consider the space in the buffer
        var max_send_length := minu32(max_allowed_length as uint32, available_length);
        return max_send_length;
    }

    /*
        peer application is initiating a stream
        peer_max_streams_bidi: maximum number of bidirectional streams the peer may initiate
        peer_max_streams_uni: maximum number of unidirectional streams the peer may initiate
        the stream will have peer_max_stream_data_bidi_local/peer_max_stream_data_bidi_remote as limit, set by peer
    */
    method open_stream_peer_initiated_impl(stream_id:stream_id_t)
        returns (x:quic_stream_mutable?)

        requires Valid();
        modifies this`peer_streams_bidi, this`peer_streams_uni;
        modifies this`segment_nodes_repr, this`segment_lists_repr, this`quic_streams_repr;

        modifies this.stream_lists_repr, this.stream_nodes_repr;
        modifies this`stream_nodes_repr;

        ensures Valid();
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr))
        ensures fresh(segment_lists_repr - old(segment_lists_repr))
        ensures fresh(quic_streams_repr - old(quic_streams_repr))

        ensures fresh(stream_nodes_repr - old(stream_nodes_repr))
        ensures x != null ==> x in quic_streams_repr;
    {
        var stream := find_stream_impl(stream_id);

        if stream != null { return stream; }
        var max_stream_data;

        if isStreamBidi(stream_id) {
            if peer_streams_bidi >= peer_max_streams_bidi {
                print("[DEBUG DFY] peer_max_streams_bidi reached\n");
                return null;
            }
            peer_streams_bidi := peer_streams_bidi + 1;
            max_stream_data := peer_max_stream_data_bidi_local;
        } else {
            if peer_streams_uni >= peer_max_streams_uni {
                print("peer_max_streams_uni reached");
                return null;
            }
            peer_streams_uni := peer_streams_uni + 1;
            max_stream_data := peer_max_stream_data_uni;
        }
        x := add_new_stream(stream_id, DEFAULT_MAX_STREAM_DATA);
    }

    /*
        local application is initiating a stream
        local_max_streams_bidi: maximum number of bidirectional streams local may initiate
        local_max_streams_uni: number of bidirectional streams local initiated
        the stream will have DEFAULT_MAX_STREAM_DATA as limit, set by local
    */
    method open_stream_local_initiated_impl(stream_id:stream_id_t)
        returns (x:quic_stream_mutable?)

        requires Valid();
        modifies this`local_streams_uni, this`local_streams_bidi;
        modifies this`segment_nodes_repr, this`segment_lists_repr, this`quic_streams_repr;

        modifies this.stream_lists_repr, this.stream_nodes_repr;
        modifies this`stream_nodes_repr;

        ensures Valid();
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr))
        ensures fresh(segment_lists_repr - old(segment_lists_repr))
        ensures fresh(quic_streams_repr - old(quic_streams_repr))
        ensures fresh(stream_nodes_repr - old(stream_nodes_repr))

        ensures x != null ==> x in quic_streams_repr;
    {
        var stream := find_stream_impl(stream_id);
        if stream != null { return stream; }

        if isStreamBidi(stream_id) {
            if local_streams_bidi >= local_max_streams_bidi {
                print("local_max_streams_bidi reached");
                return null;
            }
            local_streams_bidi := local_streams_bidi + 1;
        } else {
            if local_streams_uni >= local_max_streams_uni {
                print("local_max_streams_uni reached");
                return null;
            }
            local_streams_uni := local_streams_uni + 1;
        }

        x := add_new_stream(stream_id, DEFAULT_MAX_STREAM_DATA);
    }

    method add_send_data_to_stream_impl(stream: quic_stream_mutable, data:buffer_t, datalength:uint32, fin:bool)
        returns (x: handle_t)
        requires Valid();
        requires data != null && data.Length == datalength as int;
        requires stream in quic_streams_repr;

        modifies this`segment_nodes_repr,
            this.quic_streams_repr, this.segment_nodes_repr, this.segment_lists_repr;

        ensures fresh(segment_nodes_repr - old(segment_nodes_repr))
        ensures Valid();
    {
        x := stream.add_send_data(data, datalength, fin);
        var pending := stream.has_send_data_pending();
        segment_nodes_repr := flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr);
    }

    method get_send_data_from_crypto_stream(ps:packet_space)
        returns (x:Err<qstream_segment_fixed>)

        requires Valid();

        modifies this`segment_nodes_repr;
        modifies this.quic_streams_repr, this.segment_nodes_repr, this.segment_lists_repr;
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr))

        ensures Valid();
    {
        var crypto_stream := get_crypto_stream(ps);

        var is_empty := crypto_stream.segments.IsEmpty();
        if is_empty { return Fail("no ready segment"); }

        // call segments_remove_head directly without flow control
        var segment := crypto_stream.segments_remove_head();
        segment_nodes_repr := flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr);

        return Ok(segment);
    }

    // though not enforced, this should only be called on crypto stream
    method get_receive_ready_data_from_crypto_stream(stream: quic_stream_mutable) returns (x: qstream_segment_fixed)
        requires Valid()
        requires |stream.readysegments.Vals| != 0;
        requires stream in quic_streams_repr;

        modifies this`segment_nodes_repr,
            this.quic_streams_repr, this.segment_nodes_repr, this.segment_lists_repr;
        ensures Valid()
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr))
    {
        x := stream.get_receive_ready_data();
        segment_nodes_repr := flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr);
    }

    method add_ready_receive_data_to_stream_impl(stream: quic_stream_mutable, segment: qstream_segment_fixed)
        requires Valid()
        requires stream in quic_streams_repr;

        modifies this`segment_nodes_repr,
            this.quic_streams_repr, this.segment_nodes_repr, this.segment_lists_repr;
        ensures Valid()
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr))
        ensures |stream.readysegments.Vals| != 0;
    {
        stream.add_ready_receive_data(segment);
        segment_nodes_repr := flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr);
    }

    method try_add_to_ready_streams(stream:quic_stream_mutable)
        requires Valid();
        requires stream in quic_streams_repr;

        modifies this.stream_lists_repr, this.stream_nodes_repr;
        modifies this`stream_nodes_repr;

        ensures fresh(stream_nodes_repr - old(stream_nodes_repr))
        ensures Valid();
    {
        var empty := stream.readysegments.IsEmpty();

        if ! empty {
            ready_streams.InsertTail(stream);
            stream_nodes_repr := streams.Repr + ready_streams.Repr;
            set_event_handle(connection_receive_data_ready);
        }

    }

    // process the ready stream queue, no crypto stream should involve
    method process_receive_ready_streams() returns (x: stream_recv)
        requires Valid();
        requires |ready_streams.Vals| != 0;

        modifies this.stream_lists_repr,
            this.stream_nodes_repr,
            this.quic_streams_repr,
            this.segment_nodes_repr,
            this.segment_lists_repr;

        modifies this`stream_nodes_repr,
            this`segment_nodes_repr;

        ensures fresh(this.stream_nodes_repr - old(this.stream_nodes_repr))
        ensures fresh(this.segment_nodes_repr - old(this.segment_nodes_repr))
        ensures Valid();
    {
        var stream := ready_streams.RemoveHead();
        stream_nodes_repr := streams.Repr + ready_streams.Repr;

        assert stream in quic_streams_repr;
        assert stream.Valid(); // observe

        var ready_empty := stream.readysegments.IsEmpty();
        if ready_empty { fatal("this should not have happened!"); }

        var tuple := stream.receive_from_stream();
        x := tuple.0;
        var new_data := tuple.1;
        segment_nodes_repr := flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr);

        try_add_to_ready_streams(stream);
    }

    method add_partial_receive_data_to_stream(stream: quic_stream_mutable, segment: qstream_segment_fixed) returns (new_data: bool)
        requires Valid();
        requires stream_in_manager(stream);
        modifies this`segment_nodes_repr,
            this.quic_streams_repr, this.segment_nodes_repr, this.segment_lists_repr;
        ensures Valid();
        ensures new_data ==> |stream.readysegments.Vals| != 0
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr));
    {
        new_data := stream.add_partial_receive_data(segment);
        segment_nodes_repr := flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr);
    }

    method add_partial_receive_data_to_crypto_stream(ps: packet_space, segment: qstream_segment_fixed)
        returns (x: Option<qstream_segment_fixed>)

        requires Valid();
        modifies this`segment_nodes_repr,
            this.quic_streams_repr, this.segment_nodes_repr, this.segment_lists_repr;
        ensures Valid();
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr));
    {
        var crypto_stream := get_crypto_stream(ps);
        var new_data := add_partial_receive_data_to_stream(crypto_stream, segment);

        if ! new_data {
            return None;
        }

        // remove seg from the head of the list
        var segment := get_receive_ready_data_from_crypto_stream(crypto_stream);
        return Some(segment);
    }

    method set_max_stream_data(stream_id: stream_id_t, maxdata: uint62)
        requires Valid();

        modifies this`peer_streams_bidi, this`peer_streams_uni;
        modifies this`segment_nodes_repr, this`segment_lists_repr, this`quic_streams_repr;
        modifies this.quic_streams_repr;
        modifies this.stream_lists_repr, this.stream_nodes_repr;
        modifies this`stream_nodes_repr;

        ensures Valid();
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr))
        ensures fresh(segment_lists_repr - old(segment_lists_repr))
        ensures fresh(quic_streams_repr - old(quic_streams_repr))
        ensures fresh(stream_nodes_repr - old(stream_nodes_repr))
    {
        var stream := open_stream_peer_initiated_impl(stream_id);

        if stream == null { fatal("Could not find stream"); }

        stream.set_max_send_stream_data(maxdata);
    }

    // Reset a stream in response to RST_STREAM
    method reset_stream(stream_id:stream_id_t, errorCode:uint62, finalOffset:uint62)
        requires Valid();

        modifies this`peer_streams_bidi, this`peer_streams_uni;
        modifies this`segment_nodes_repr, this`segment_lists_repr, this`quic_streams_repr;
        modifies this.quic_streams_repr;
        modifies this.stream_lists_repr, this.stream_nodes_repr;
        modifies this`stream_nodes_repr;

        ensures Valid();
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr))
        ensures fresh(segment_lists_repr - old(segment_lists_repr))
        ensures fresh(quic_streams_repr - old(quic_streams_repr))
        ensures fresh(stream_nodes_repr - old(stream_nodes_repr))
    {
        var stream := open_stream_peer_initiated_impl(stream_id);
        if stream == null { fatal("Could not open stream"); }

        stream.recv_state := RecvStreamResetRecvd;
        stream.error_code := errorCode;
        print ("[DEBUG DFY] RST_STREAM StreamID=", stream_id, " errorCode=", errorCode, "\n");
    }

    method retransmit_stream_frame(segment:qstream_segment_fixed)
        requires Valid();
        modifies this`segment_nodes_repr, this`total_data_sent,
            this.quic_streams_repr, this.segment_nodes_repr, this.segment_lists_repr;
        ensures Valid();
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr));
    {
        var stream := find_stream_impl(segment.stream_id);
        if stream == null { fatal("Could not find stream"); }
        // Place this segment back in the list of segments to send

        stream.segments_insert_head(segment); 
        segment_nodes_repr := flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr);

        if total_data_sent < segment.datalength as uint62 { fatal("this should not have happened"); }
        total_data_sent := total_data_sent - segment.datalength as uint62;
    }

    method retransmit_crypto_frame(ps:packet_space, segment:qstream_segment_fixed)
        requires Valid();
        modifies this`segment_nodes_repr, this`total_data_sent,
            this.quic_streams_repr, this.segment_nodes_repr, this.segment_lists_repr;
        ensures Valid();
        ensures fresh(segment_nodes_repr - old(segment_nodes_repr));
    {
        var crypto_stream := get_crypto_stream(ps);
        // Place this segment back in the list of segments to send
        crypto_stream.segments_insert_head(segment);
        segment_nodes_repr := flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr);
    }

    method set_initial_crypto_stream_offset(new_offset: uint62)
        requires Valid();
        modifies this.quic_streams_repr;
        ensures Valid();
    {
        var crypto_stream := get_crypto_stream(INITIAL_SPACE);
        crypto_stream.nextReadOffset := new_offset;
    }

    method on_reset_stream_acked(stream_id: stream_id_t)
        requires Valid();
        modifies this.quic_streams_repr;
        ensures Valid();
    {
        var stream :quic_stream_mutable? := find_stream_impl(stream_id);
        if stream != null && stream.send_state == SendStreamResetSent {
            stream.send_state := SendStreamResetRecvd;
        }
    }

    // this method takes long
    method get_send_ready_segment_impl(available_length: uint32)
        returns (x : Option<(stream_id_t, qstream_segment_fixed)>)
        requires Valid();

        modifies this`segment_nodes_repr;
        modifies this.quic_streams_repr, this.segment_nodes_repr, this.segment_lists_repr;

        ensures fresh(segment_nodes_repr - old(segment_nodes_repr));
        ensures Valid();
    {
        var max_send_length := get_send_length(available_length);

        var stream := find_send_ready_stream();

        if stream == null || max_send_length == 0 {
            print("[DEBUG DFY] no stream data can be sent\n");
            return None;
        }

        var segment := stream.get_send_ready_data(max_send_length);
        segment_nodes_repr := flatten_clear(set s | s in quic_streams_repr :: s.nodes_repr);
        return Some((stream.stream_id, segment));
    }

    // available_length is the available_length that can be sent
    method {:timeLimit 50} get_send_ready_segment(available_length: uint32)
        returns (x : Option<(stream_id_t, qstream_segment_fixed)>)
        requires Valid();

        modifies this`total_data_sent,
             this`segment_nodes_repr;
        modifies this.quic_streams_repr, this.segment_nodes_repr, this.segment_lists_repr;

        ensures fresh(segment_nodes_repr - old(segment_nodes_repr));
        ensures Valid();
    {
        x := get_send_ready_segment_impl(available_length);
        if x.Some? {
            var data_len := x.value.1.datalength as uint62;

            FailOnOverflowAdd_u62(total_data_sent, data_len);
            total_data_sent := total_data_sent + data_len;
        }
    }

    method stream_receive_impl(id:uint62, segment:qstream_segment_fixed)
        requires Valid();

        modifies segment_nodes_repr,
            segment_lists_repr,
            quic_streams_repr;

        modifies this`peer_streams_bidi,
            this`peer_streams_uni,
            this`quic_streams_repr,
            this`segment_nodes_repr,
            this`segment_lists_repr;

        modifies this.stream_lists_repr, this.stream_nodes_repr;
        modifies this`stream_nodes_repr;

        ensures fresh(this.quic_streams_repr - old(this.quic_streams_repr));
        ensures fresh(this.segment_nodes_repr - old(this.segment_nodes_repr));
        ensures fresh(this.segment_lists_repr - old(this.segment_lists_repr));
        ensures fresh(this.stream_nodes_repr - old(this.stream_nodes_repr));

        ensures Valid();
    {
        var stream := open_stream_peer_initiated_impl(id);

        if stream == null {
            print("[DEBUG DFY] dropping received data for invalid stream ID ", id, "\n");
            return;
        }

        var new_data := add_partial_receive_data_to_stream(stream, segment);
        if !new_data { return; }

        print("[DEBUG DFY] new data received for stream ID ", id, "\n");

        try_add_to_ready_streams(stream);
    }
}
}
