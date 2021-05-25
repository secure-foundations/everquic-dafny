include "NativeTypes.dfy"
include "PrivateDLL.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "HandleFFIs.dfy"
include "Extern.dfy"
include "Options.dfy"

module QStream {
import opened NativeTypes
import opened PrivateDLL
import opened QUICDataTypes
import opened QUICConstants
import opened HandleFFIs
import opened Extern
import opened Options

type segment_node = PrivateNode<qstream_segment_fixed>
type qstream_segment_list = PrivateDoublyLinkedList<qstream_segment_fixed>

// A QUIC stream of outgoing data
class quic_stream_mutable {
    var stream_id: stream_id_t;
    // Mutable portion of a QUIC stream
    // Receive-stream fields
    // Current recv-stream state
    var recv_state: quic_recv_stream_state;
    // Data that has been received but is still incomplete
    var partialsegments: qstream_segment_list;
    // Data that has been recieved and is ready for QUIC_RecvStream() to return
    var readysegments: qstream_segment_list;
    // Data arriving with offsets above this go into partialsegments
    var nextReadOffset: uint62;
    // Error code, set by RST_STREAM
    var error_code: uint62;

    // Current send-stream state
    var send_state: quic_send_stream_state;
    // Next stream offset where writes will go
    var nextWriteOffset: uint62;
    var max_send_stream_data: uint62;
    // Data that is ready to send for the first time
    var segments: qstream_segment_list;

    ghost var nodes_repr: set<segment_node>;
    ghost var lists_repr: set<qstream_segment_list>;

    constructor (stream_id: uint62, max_send_stream_data: uint62)
        ensures Valid();
        ensures this.stream_id == stream_id;
        ensures this.recv_state == RecvStreamRecv;
        ensures this.nextReadOffset == 0;
        ensures this.error_code == 0;
        ensures this.send_state == SendStreamSend;
        ensures this.nextWriteOffset == 0;
        ensures this.max_send_stream_data == max_send_stream_data;
        ensures fresh(lists_repr) && fresh(nodes_repr);
    {
        var l1 := new qstream_segment_list();
        var l2 := new qstream_segment_list();
        var l3 := new qstream_segment_list();

        this.stream_id := stream_id;
        this.recv_state := RecvStreamRecv;
        this.partialsegments := l1;
        this.readysegments := l2;
        this.nextReadOffset := 0;
        this.error_code := 0;
        this.send_state := SendStreamSend;
        this.nextWriteOffset := 0;
        this.max_send_stream_data := max_send_stream_data;
        this.segments := l3;

        this.lists_repr := {l1, l2, l3};
        this.nodes_repr := l1.Repr + l2.Repr + l3.Repr;
    }

    predicate reprValid()
        reads this, lists_repr;
    {
        && lists_repr == {partialsegments, readysegments, segments}
        && nodes_repr == partialsegments.Repr + readysegments.Repr + segments.Repr
    }

    predicate componentsValid()
        reads this, nodes_repr, lists_repr;
        requires reprValid();
    {
        && partialsegments.Valid()
        && readysegments.Valid()
        && segments.Valid()
        && partialsegments.Repr !! readysegments.Repr !! segments.Repr
        && readysegments != partialsegments
        && segments != readysegments
        && segments != partialsegments
    }

    predicate Valid()
        reads this, nodes_repr, lists_repr;
    {
        reprValid() && componentsValid()
    }

    method update_nodes_repr()
        modifies this`nodes_repr;
        ensures nodes_repr == partialsegments.Repr + readysegments.Repr + segments.Repr;
    {
        nodes_repr := partialsegments.Repr + readysegments.Repr + segments.Repr;
    }

    method segments_remove_head() returns (s:qstream_segment_fixed)
        requires Valid()
        requires |segments.Vals| != 0;
        modifies this`nodes_repr,
            this.lists_repr, this.nodes_repr;
        ensures Valid()
        ensures fresh(nodes_repr - old(nodes_repr))
    {
        s := segments.RemoveHead();
        update_nodes_repr();
    }

    method segments_insert_head(s:qstream_segment_fixed)
        requires Valid()
        modifies this`nodes_repr, lists_repr, nodes_repr;
        ensures Valid()
        ensures fresh(nodes_repr - old(nodes_repr))
    {
        segments.InsertHead(s);
        update_nodes_repr();
    }

    method segments_peek_head() returns (s:qstream_segment_fixed)
        requires Valid();
        requires |segments.Vals| != 0;
        ensures Valid();
    {
        s := segments.PeekHead();
    }

    // retutrns if stream has data to be sent
    method has_send_data_pending() returns (x:bool)
        requires Valid();
        ensures x ==> (|segments.Vals| != 0);
    {
        x := segments.IsEmpty();
        x := !x;
    }

    method add_send_data(data:buffer_t, datalength:uint32, fin:bool) returns (x: handle_t)
        requires Valid()
        requires data != null && data.Length == datalength as int;
        modifies this`nodes_repr, this`nextWriteOffset, this`send_state,
            this.lists_repr, this.nodes_repr;
        ensures Valid()
        ensures fresh(nodes_repr - old(nodes_repr))
    {
        if send_state != SendStreamSend {
            fatal("[DEBUG DFY] Stream is not in sending state\n");
        }

        var new_offset :uint64 := nextWriteOffset as uint64 + datalength as uint64;

        if new_offset > max_send_stream_data as uint64 {
            return NONE_HANDLE;
        }

        var event := NONE_HANDLE;

        var segment: qstream_segment_fixed := 
            qstream_segment_raw(nextWriteOffset, data[..], datalength, fin, true, event, stream_id);

        nextWriteOffset := new_offset as uint62;

        segments.InsertTail(segment);
        update_nodes_repr();

        if fin { send_state := SendStreamDataSent; }

        x := segment.available;
    }

    // though not enforced, this should only be called on crypto stream
    method get_receive_ready_data() returns (x: qstream_segment_fixed)
        requires Valid()
        requires |readysegments.Vals| != 0;
        modifies this`nodes_repr,
            this.lists_repr, this.nodes_repr;
        ensures fresh(nodes_repr - old(nodes_repr))
        ensures Valid()
    {
        x := readysegments.RemoveHead();
        update_nodes_repr();
    }

    method add_ready_receive_data(segment: qstream_segment_fixed)
        requires Valid()
        modifies this`nodes_repr, this`nextReadOffset,
            this.lists_repr, this.nodes_repr;
        ensures fresh(nodes_repr - old(nodes_repr))
        ensures Valid()
        ensures |readysegments.Vals| != 0;
    {
        var new_offset :uint64 := nextReadOffset as uint64 + segment.datalength as uint64;

        if new_offset > UINT62_MAX {
            fatal("nextReadOffset overflow");
        }

        nextReadOffset := new_offset as uint62;
        readysegments.InsertTail(segment);
        update_nodes_repr();
    }

    // checks partial list, move segments if possible, returns true if there is new data available
    method try_move_paritial_segments() returns (new_data: bool)
        requires Valid();
        modifies this`nodes_repr, this`nextReadOffset,
            this.lists_repr, this.nodes_repr;
        ensures Valid();
        ensures new_data ==> |readysegments.Vals| != 0;
        ensures fresh(nodes_repr - old(nodes_repr));
    {
        new_data := false;

        while true
            invariant Valid();
            invariant fresh(nodes_repr - old(nodes_repr));
            decreases |partialsegments.Vals|;
            invariant new_data ==> |readysegments.Vals| != 0;
        {
            // nothing on the partial list
            var partial_empty := partialsegments.IsEmpty();
            if partial_empty { return; }

            // something on the partial list
            var next_segment := partialsegments.PeekHead();
            var next_start := next_segment.offset;
            var next_end := compute_segment_end(next_segment);

            // there is still a gap, then break
            if next_start > nextReadOffset { return; }

            // there is no gap, we should at least remove next_segment
            next_segment := partialsegments.RemoveHead();

            // next_segment provides new data
            if next_end > nextReadOffset {
                new_data := true;

                if next_start != nextReadOffset {
                    assert next_start < nextReadOffset;
                    // segment gives new data, but has overlap, so remove overlap
                    var overlap_size := nextReadOffset - next_start;
                    var tuple := split_segment(next_segment, overlap_size as uint32);
                    var none_overlap_segment := tuple.1;
                    next_segment := none_overlap_segment;
                }

                // now the segment should have no overlap, advance read offset
                nextReadOffset := nextReadOffset + next_segment.datalength as uint62;
                readysegments.InsertTail(next_segment);
            }
            update_nodes_repr();
        }
    }

    // this should not be called on a crypto stream
    method receive_from_stream()  returns (x:(stream_recv,bool))
        requires Valid();
        requires |readysegments.Vals| != 0;
        modifies this`nodes_repr, this`nextReadOffset, this`recv_state,
            this.lists_repr, this.nodes_repr;
        ensures Valid();
        ensures x.1 ==> |readysegments.Vals| != 0;
        ensures fresh(nodes_repr - old(nodes_repr));
    {
        if recv_state == RecvStreamResetRecvd {
            recv_state := RecvStreamResetRead;
            var r := reset_recv(stream_id, error_code);
            return (Reset(r), false);
        }

        print_ready_segments();
        // remove seg from the head of the list
        var segment := readysegments.RemoveHead();
        update_nodes_repr();

        if segment.fin { recv_state := RecvStreamDataRead;}

        var a := ReceivedData(data_recv(stream_id, segment));
        var _:= try_move_paritial_segments();
        var b := readysegments.IsEmpty();

        return (a, !b);
    }

    // should not be called from the outside
    method insert_to_partialsegments (new_segment: qstream_segment_fixed)
        requires Valid();
        modifies this`nodes_repr, this`nextReadOffset, this`recv_state,
            this.lists_repr, this.nodes_repr;
        ensures Valid();
        ensures fresh(nodes_repr - old(nodes_repr));
    {
        var is_empty := partialsegments.IsEmpty();

        if is_empty {
            // the list is empty
            partialsegments.InsertHead(new_segment);
            update_nodes_repr();
            return;
        }

        var new_start := new_segment.offset;
        var new_end := compute_segment_end(new_segment);

        var last_segment : qstream_segment_fixed := partialsegments.PeekTail(); // last value

        if new_start >= last_segment.offset {
            var old_end := compute_segment_end(last_segment);
            if new_end > old_end {
                // insert into the tail of the list
                partialsegments.InsertTail(new_segment);
                update_nodes_repr();
            }
            return;
        }

        var keepgoing := true;
        var iter := new DllIterator(partialsegments);

        while keepgoing
            invariant Valid();
            invariant keepgoing ==> iter.Valid()
            invariant keepgoing ==> iter.d == partialsegments
            decreases |partialsegments.Vals| - iter.GetIndex(), keepgoing
            invariant !keepgoing ==> iter.GetIndex() == |partialsegments.Vals|
            invariant partialsegments == old(partialsegments)
            invariant fresh(nodes_repr - old(nodes_repr));
        {
            var list_segment : qstream_segment_fixed := iter.GetVal();

            var current_start := list_segment.offset;
            var current_end := compute_segment_end(list_segment);

            if new_start < current_start {
                // insert here and done
                InsertBeforeIter(partialsegments, iter, new_segment);
                update_nodes_repr();
                break;
            } else if new_end <= current_end {
                // drop directly and done
                break;
            }
            keepgoing := iter.MoveNext();
        }
    }

    method add_partial_receive_data(segment: qstream_segment_fixed) returns (new_data: bool)
        requires Valid()
        modifies this`nodes_repr, this`nextReadOffset, this`recv_state,
            this.lists_repr, this.nodes_repr;
        ensures Valid()
        ensures fresh(nodes_repr - old(nodes_repr))
        ensures new_data ==> |readysegments.Vals| != 0;
    {
        var segment_start, segment_end := segment.offset, compute_segment_end(segment);

        print_partial_segments();
        print("[DEBUG STREAM] new segment(", segment_start , ", ", segment_end, ")\n");

        // dropping data as the stream isn't in RecvStreamRecv
        if recv_state != RecvStreamRecv { return false; }

        // dropping immediately
        if segment_end <= nextReadOffset {
            print("[DEBUG DFY] stream ignore duplicated data\n");
            return false;
        }

        insert_to_partialsegments(segment);
        print_partial_segments();

        new_data := try_move_paritial_segments();

        print_partial_segments();
    }

    method print_partial_segments()
        requires Valid();
    {
        print("[DEBUG DFY] read offset ", nextReadOffset, "\n");
        print_segment_list("partial", partialsegments);
    }

    method print_ready_segments()
        requires Valid();
    {
        print("[DEBUG DFY] read offset ", nextReadOffset, "\n");
        print_segment_list("ready", readysegments);
    }

    method print_segment_list(name: string, segments: qstream_segment_list)
        requires segments.Valid();
    {
        print("[DEBUG STREAM] ",name , " segment list: ");

        var is_empty := segments.IsEmpty();

        if is_empty {
            print("empty\n");
            return;
        }

        var keepgoing := true;
        var iter := new DllIterator(segments);

        while keepgoing
            invariant segments.Valid()
            invariant keepgoing ==> iter.Valid()
            invariant keepgoing ==> iter.d == segments
            decreases |segments.Vals| - iter.GetIndex(), keepgoing
        {
            var list_segment : qstream_segment_fixed := iter.GetVal();
            print_segment(list_segment);
            keepgoing := iter.MoveNext();
        }
        print("\n");
    }

    method set_max_send_stream_data(maxdata: uint62)
        requires Valid();
        modifies this`max_send_stream_data;
        ensures Valid();
    {
        max_send_stream_data :=
            if maxdata < max_send_stream_data then max_send_stream_data else maxdata;
    }

    method get_send_ready_data(max_send_length:uint32)
        returns (x : qstream_segment_fixed)

        requires max_send_length != 0;
        requires Valid() && |segments.Vals| != 0

        modifies this`nodes_repr, lists_repr, nodes_repr;

        ensures fresh(nodes_repr - old(nodes_repr))
        ensures x.datalength as int <= max_send_length as int;
        ensures Valid();
    {
        var segment := segments_peek_head(); // peek don't pop

        var _ := segments_remove_head();

        if segment.datalength > max_send_length {
            // only part of the segment can fit in this packet. Split the segment,
            // returning the head portion, and enqueing the tail portion back
            // into the stream for transmission later.
            var segments := split_segment(segment, max_send_length);
            segment := segments.0;
            segments_insert_head(segments.1);
        }
        return segment;
    }

    // Free the memory associated with a segment
    static method deleteSegment (segment:qstream_segment_fixed)
    {
        var handle := segment.available;
        if handle != NONE_HANDLE {
            close_event_handle(handle);
        }
    }

    static method split_segment(segment:qstream_segment_fixed, offset:uint32)
        returns (x: (qstream_segment_fixed, qstream_segment_fixed))
        requires 0 < offset < segment.datalength;
        ensures x.0.datalength == offset;
        ensures x.1.datalength == segment.datalength - offset;
    {
        var data := segment.data;

        var x1 := qstream_segment_raw(
            segment.offset,
            data[0..offset],
            offset,
            segment.isApplicationOwned,
            false,
            NONE_HANDLE,
            segment.stream_id
        );

        var x2 := qstream_segment_raw(
            segment.offset + offset as uint62,
            data[offset..],
            segment.datalength - offset,
            segment.isApplicationOwned,
            segment.fin,
            segment.available, // move the handle to the second one
            segment.stream_id
        );

        return (x1, x2);
    }

}
}
