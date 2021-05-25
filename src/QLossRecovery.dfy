include "NativeTypes.dfy"
include "PrivateDLL.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "Options.dfy"
include "OverFlowCheck.dfy"
include "Extern.dfy"
include "QUICUtils.dfy"
include "HandleFFIs.dfy"

module QLossRecovery {

import opened NativeTypes
import opened PrivateDLL
import opened QUICDataTypes
import opened QUICConstants
import opened Options
import opened OverFlowCheck
import opened Extern
import opened QUICUtils
import opened HandleFFIs

type loss_tracker_list = PrivateDoublyLinkedList<loss_tracker_fixed>
type sent_packet_list = PrivateDoublyLinkedList<sent_packet_fixed>

/* Mutable state related to the LossAndCongestion module.  Fields are generally
    all taken directly from the QUIC RFC. */
class LRCCManager
{
    // maximum reordering in packets before packet threshold loss detection considers a packet lost. The RECOMMENDED value is 3.
    static const kPacketThreshold: uint62 := 3;

    // maximum reordering in time before time threshold loss detection considers a packet lost. Specified as an RTT multiplier. The RECOMMENDED value is 9/8.
    static const kTimeThresholdNumerator: uint64 := 11; 
    static const kTimeThresholdDenominator: uint64 := 8; 

    // Timer granularity. This is a system-dependent value. However, implementations SHOULD use a value no smaller than 1ms.
    static const kGranularity :uint64 := 2;

    // The RTT used before an RTT sample is taken. The RECOMMENDED value is 500ms.
    static const kInitialRtt: uint64 := 500;

    // The sender's current maximum payload size. Does not include UDP or IP overhead. The max datagram size is used for congestion window computations. An endpoint sets the value of this variable based on its PMTU (see Section 14.1 of [QUIC-TRANSPORT]), with a minimum value of 1200 bytes.
    static const max_datagram_size: uint32 := 4096;

    // Default limit on the initial amount of data in flight, in bytes. Taken from [RFC6928], but increased slightly to account for the smaller 8 byte overhead of UDP vs 20 bytes for TCP. The RECOMMENDED value is the minimum of 10 * max_datagram_size and max(2 * max_datagram_size, )).
    static const kInitialWindow: uint64 := 94720;

    // Minimum congestion window in bytes. The RECOMMENDED value is 2 * max_datagram_size.
    static const kMinimumWindow: uint64 := (2 * max_datagram_size) as uint64;

    // Reduction in congestion window when a new loss event is detected. The RECOMMENDED value is 0.5.
    static const kLossReductionFactorNumerator :uint64 := 1;
    static const kLossReductionFactorDenominator :uint64 := 2;

    // Period of time for persistent congestion to be established, specified as a PTO multiplier. The rationale for this threshold is to enable a sender to use initial PTOs for aggressive probing, as TCP does with Tail Loss Probe (TLP) [RACK], before establishing persistent congestion, as TCP does with a Retransmission Timeout (RTO) [RFC5681]. The RECOMMENDED value for kPersistentCongestionThreshold is 3, which is approximately equivalent to having two TLPs before an RTO in TCP.
    static const kPersistentCongestionThreshold: uint32 := 2;

    // multi-modal timer used for loss detection.
    var loss_detection_timer: voidptr; 

    var ping_alarm: voidptr;

    // the most recent RTT measurement made when receiving an ack for a previously unacked packet
    var latest_rtt: uint64;

    // the smoothed RTT of the connection, computed as described in [RFC6298]
    var smoothed_rtt: uint64;

    // the RTT variation, computed as described in [RFC6298]
    var rttvar: uint64;

    // the minimum RTT seen in the connection, ignoring ack delay.
    var min_rtt: uint64;

    // the maximum amount of time by which the receiver intends to delay acknowledgments for packets in the ApplicationData packet number space. The actual ack_delay in a received ACK frame may be larger due to late timers, reordering, or lost ACK frames.
    var max_ack_delay: uint64;

    // The number of times a PTO has been sent without receiving an ack.
    var pto_count: uint64;

    // The time the most recent ack-eliciting packet was sent.
    var time_of_last_sent_ack_eliciting_packet: uint64;

    // The largest packet number acknowledged in the packet number space so far.
    var largest_acked_packet: uint62;

    // The time at which the next packet in that packet number space will be considered lost based on exceeding the reordering window in time.
    var loss_time: uint64;

    // An association of packet numbers in a packet number space to information about them
    var sent_packets: sent_packet_list; 

    // The highest value reported for the ECN-CE counter in the packet number space by the peer in an ACK frame. This value is used to detect increases in the reported ECN-CE counter.
    // var ecn_ce_counters: uint64;

    // The sum of the size in bytes of all sent packets that contain at least one ack-eliciting or PADDING frame, and have not been acked or declared lost. The size does not include IP or UDP overhead, but does include the QUIC header and AEAD overhead. Packets only containing ACK frames do not count towards bytes_in_flight to ensure congestion control does not impede congestion feedback.
    var bytes_in_flight: uint64;

    // Maximum number of bytes-in-flight that may be sent.
    var congestion_window: uint64;

    // The time when QUIC first detects congestion due to loss or ECN, causing it to enter congestion recovery. When a packet sent after this time is acknowledged, QUIC exits congestion recovery.
    var congestion_recovery_start_time: uint64;

    // Slow start threshold in bytes. When the congestion window is below ssthresh, the mode is slow start and the window grows by the number of bytes acknowledged.
    var ssthresh: uint64;

    constructor (use_time_loss: bool)
        ensures Valid()
        ensures fresh(sent_packets)
            && fresh(sent_packets.Repr);
    {
        loss_detection_timer := null;
        ping_alarm := null;

        pto_count := 0;
        latest_rtt := 0;
        smoothed_rtt := 0;
        rttvar := 0;
        min_rtt := 0;
        max_ack_delay := 0;
        largest_acked_packet := UINT62_MAX as uint62;
        time_of_last_sent_ack_eliciting_packet := 0;
        loss_time := 0;
        sent_packets := new sent_packet_list();
        
        congestion_window := kInitialWindow;
        bytes_in_flight := 0;
        congestion_recovery_start_time := 0;
        ssthresh := UINT64_MAX;
    }

    predicate Valid()
        reads this, sent_packets, sent_packets.Repr;
    {
        && sent_packets.Valid()
    }

    static method get_sent_packet_flags(trackers: seq<loss_tracker_fixed>, count: uint32) 
        returns (x: (bool, bool))
        requires |trackers| == count as int;
    {
        /*
        ack_eliciting: Packets that contain ack-eliciting frames elicit an ACK from the receiver within the maximum ack delay and are called ack-eliciting packets. All frames other than ACK, PADDING, and CONNECTION_CLOSE are considered ack-eliciting.
        
        in_flight: Packets are considered in-flight when they have been sent and are not ACK-only, and they are not acknowledged, declared lost, or abandoned along with old keys.
        */

        var ack_eliciting := false;
        var ack_only := true; 
        var i := 0;

        while i < count
        {
            match trackers[i] {
                case crypto_tracker(c) => ack_eliciting := true;
                case stream_tracker(s) => ack_eliciting := true;
                case ack_tracker(a) => var _ := true;
                case fixed_frame_tracker(f) => ack_eliciting := true;
            }
            i := i + 1;
        }

        ack_only := !ack_eliciting; 
        return (ack_eliciting, ack_only);
    }

    static method build_sent_packet(
        ps: packet_space, 
        packet_number: uint62,
        trackers: loss_tracker_list,
        sent_bytes: uint32)
        returns(x: sent_packet_fixed)

        requires trackers.Valid();
    {
        if sent_bytes > UINT16_MAX as uint32 {
            fatal("too many bytes in a packet");
        }

        var is_empty := trackers.IsEmpty();

        if is_empty {
            fatal("lr list should not be empty here");
        }

        var empty := stream_tracker(qstream_segment_raw(0, [], 0, false, false, 0, 0));
        var converted := list_to_seq(trackers, empty);
        var strackers, count := converted.0, converted.1;

        var flags := get_sent_packet_flags(strackers, count);
        var ack_eliciting, ack_only := flags.0, flags.1;

        var now := get_system_time();

        x := sent_packet_raw(
            now,
            ps,
            packet_number,
            sent_bytes as uint16,
            converted.0,
            count,
            ack_eliciting,
            ack_only
        );
    }

    method remove_sent_packet(pn_space: packet_space, pn:uint62) returns (x: Option<sent_packet_fixed>)
        requires Valid();
        modifies sent_packets, sent_packets.Repr;
        ensures fresh(sent_packets.Repr - old(sent_packets.Repr));
        ensures Valid();
    {
        var is_empty := sent_packets.IsEmpty();
        if is_empty { return None; }

        var good := true;
        var iter := new DllIterator(sent_packets);

        while good
            invariant sent_packets.Valid()
            invariant good ==> iter.Valid()
            invariant good ==> iter.d == sent_packets
            invariant forall o :: o in sent_packets.Repr ==> o in old(sent_packets.Repr);
            invariant |old(sent_packets.Vals)| >= |sent_packets.Vals|
            invariant !good ==> iter.GetIndex() == |sent_packets.Vals|
            decreases |sent_packets.Vals|, old(|sent_packets.Vals|) - iter.GetIndex(), good
        {
            var sent_packet := iter.GetVal();
            if sent_packet.packet_number == pn {
                good := RemoveIter(sent_packets, iter);
                return Some(sent_packet);
            }

            good := iter.MoveNext();
        }
        return None;
    }

    // Determine if a packet number has been sent previously or not
    method find_sent_packet(pn_space: packet_space, pn:uint62) returns (x: Option<sent_packet_fixed>)
        requires Valid();
    {
        var is_empty := sent_packets.IsEmpty();
        if is_empty { return None; }

        var good := true;
        var iter := new DllIterator(sent_packets);

        while good
            invariant sent_packets.Valid()
            invariant good ==> iter.Valid()
            invariant good ==> iter.d == sent_packets
            decreases |sent_packets.Vals| - iter.GetIndex(), good
        {
            var sent_packet := iter.GetVal();
            if sent_packet.pn_space == pn_space && sent_packet.packet_number == pn {
                return Some(sent_packet);
            }

            good := iter.MoveNext();
        }
        return None;
    }

    method print_packets(name: string, packets: sent_packet_list)
        requires packets.Valid();
    {
        print("[DEBUG DFY] ",name , " packet list: [");

        var is_empty := packets.IsEmpty();
        if is_empty {
            print("]\n");
            return;
        }

        var good := true;
        var iter := new DllIterator(packets);

        while good
            invariant packets.Valid()
            invariant good ==> iter.Valid()
            invariant good ==> iter.d == packets
            decreases |packets.Vals| - iter.GetIndex(), good
        {
            var packets := iter.GetVal();
            print(packets.packet_number, ", ");

            good := iter.MoveNext();
        }
        print("]\n");
        return;
    }

    method print_sent_packet()
        requires Valid();
    {
        print_packets("sent", sent_packets);
    }

    method OnPacketSentCC (packet:sent_packet_fixed)
        requires Valid();
        modifies this`bytes_in_flight;
        ensures Valid();
    {
        // if ack only, do not count towards flow control limit
        if !packet.ack_only {
            bytes_in_flight := safe_add_uint64(bytes_in_flight, packet.size as uint64);
            print("[DEBUG DFY] packet sent bytes_in_flight: ", bytes_in_flight, "\n");
        }
    }

    function method InCongestionRecovery(sent_time: uint64) : (x: bool)
        reads this;
    {
        sent_time <= congestion_recovery_start_time
    }

    method OnPacketAckedCC(acked_packet: sent_packet_fixed)
        requires Valid();
        modifies this`bytes_in_flight,
            this`congestion_window;
        ensures Valid();
    {
        if acked_packet.ack_only {
            return;
        }

        var packet_size : uint64 := acked_packet.size as uint64;
        // Remove from bytes_in_flight.
        bytes_in_flight := safe_sub_uint64(bytes_in_flight, packet_size);
        print("[DEBUG DFY] packet acked bytes_in_flight: ", bytes_in_flight, "\n");

        if (InCongestionRecovery(acked_packet.sent_time)) {
            // Do not increase congestion window in recovery period.
            return;
        }
    }

    method UpdateRtt(new_rtt: uint64, ack_delay: uint64)
        requires Valid();
        modifies this`latest_rtt,
            this`min_rtt,
            this`rttvar,
            this`smoothed_rtt;
        ensures Valid();
    {
        latest_rtt := new_rtt;
        // First RTT sample.
        if smoothed_rtt == 0 {
            min_rtt := latest_rtt;
            smoothed_rtt := latest_rtt;
            rttvar := latest_rtt / 2;
            print("[DEBUG DFY] latest_rtt=", latest_rtt);
            print(" smoothed_rtt=", smoothed_rtt, " rttvar=", rttvar, "\n");

            var expected_delay := get_loss_delay();
            print("[DEBUG DFY] expected delay: ", expected_delay, "\n");
            return;
        }

        // min_rtt ignores ack delay.
        min_rtt := minu64(min_rtt, latest_rtt);
        // Limit ack_delay by max_ack_delay
        var ack_delay := minu64(ack_delay, max_ack_delay);
        // Adjust for ack delay if plausible.
        var adjusted_rtt := latest_rtt;
        
        if latest_rtt > min_rtt && latest_rtt - min_rtt > ack_delay {
            adjusted_rtt := latest_rtt - ack_delay;
        }

        var diff := if smoothed_rtt > adjusted_rtt
            then smoothed_rtt - adjusted_rtt
            else adjusted_rtt - smoothed_rtt;

        rttvar := 3 * (rttvar / 4) + diff / 4;
        smoothed_rtt := 7 * (smoothed_rtt / 8) + adjusted_rtt / 8;
    
        print("[DEBUG DFY] latest_rtt=", latest_rtt);
        print(" smoothed_rtt=", smoothed_rtt, " rttvar=", rttvar, "\n");

        var expected_delay := get_loss_delay();
        print("[DEBUG DFY] expected delay: ", expected_delay, "\n");
    }

    method get_loss_packets() returns (x:(seq<sent_packet_fixed>, uint32))

        requires Valid();
        modifies this`loss_time, 
            this`bytes_in_flight,
            this`congestion_recovery_start_time,
            this`congestion_window,
            this`ssthresh;

        modifies sent_packets, sent_packets.Repr;
        ensures fresh(sent_packets.Repr - old(sent_packets.Repr));

        ensures Valid();
        ensures |x.0| == x.1 as int;
    {
        var is_empty := sent_packets.IsEmpty();
        if is_empty { return ([], 0); }
    
        var loss_list := remove_lost_packets();
        x := list_to_seq(loss_list, sent_packet_raw(0, INITIAL_SPACE, 0, 0, [] , 0, false, false));
        
        var packets, count := x.0, x.1;

        print_packets("loss", loss_list);

        if count != 0 {
            var last_packet := packets[count - 1];
            CongestionEvent(last_packet.sent_time);
        }
    }

    method get_loss_delay() returns (loss_delay: uint64)
    {
        loss_delay := safe_mul_uint64(maxu64(latest_rtt, smoothed_rtt), kTimeThresholdNumerator);
        loss_delay := safe_div_uint64(loss_delay, kTimeThresholdDenominator);

        // Minimum time of kGranularity before packets are deemed lost.
        loss_delay := maxu64(loss_delay, kGranularity);
    }

    method remove_lost_packets() returns (loss_list: sent_packet_list)
        requires Valid();
        requires |sent_packets.Vals| != 0;
        modifies this`loss_time, this`bytes_in_flight;

        modifies sent_packets, sent_packets.Repr;
        ensures fresh(sent_packets.Repr - old(sent_packets.Repr));

        ensures Valid();

        ensures loss_list.Valid();
        ensures fresh(loss_list.Repr) && fresh(loss_list);
    {
        loss_list := new sent_packet_list();

        if (largest_acked_packet == UINT62_MAX) {
            return;
        }

        this.loss_time := 0;

        var loss_delay := get_loss_delay();
        print("[DEBUG DFY] loss_delay: ",  loss_delay, "\n");

        // packets sent before this time are deemed lost.
        var lost_send_time := get_system_time();
        lost_send_time := safe_sub_uint64(lost_send_time, loss_delay);
        lost_send_time := safe_sub_uint64(lost_send_time, 25);

        // packets with lower number are considered lost
        var lost_packet_number := 0;
    
        if largest_acked_packet > kPacketThreshold {
            lost_packet_number := largest_acked_packet - kPacketThreshold;
        } 
     
        var good := true;
        var iter := new DllIterator(sent_packets);

        print_sent_packet();

        while good
            invariant Valid();
            invariant sent_packets.Valid()
            invariant good ==> iter.Valid()
            invariant good ==> iter.d == sent_packets
            invariant |old(sent_packets.Vals)| >= |sent_packets.Vals|
            invariant !good ==> iter.GetIndex() == |sent_packets.Vals|
            invariant fresh(sent_packets.Repr - old(sent_packets.Repr));
            invariant fresh(loss_list.Repr) && loss_list.Valid();
            invariant loss_list.Repr !! sent_packets.Repr;
            decreases |sent_packets.Vals|, old(|sent_packets.Vals|) - iter.GetIndex(), good
        {
            var unacked := iter.GetVal();
            var sent_time := unacked.sent_time;
            // Mark packet as lost, or set time when it should be marked.
            if (sent_time <= lost_send_time || unacked.packet_number <= lost_packet_number  ) {
                good := RemoveIter(sent_packets, iter);
                OnPacketLost(unacked);

                loss_list.InsertTail(unacked);
            } else {
                var new_loss_time := safe_add_uint64(sent_time, loss_delay);
                if loss_time == 0 {
                    loss_time := new_loss_time;
                } else {
                    loss_time := minu64(loss_time, new_loss_time);
                }
                good := iter.MoveNext();
            }
        }
    }

    method OnPacketLost(lost_packet: sent_packet_fixed)
        modifies this`bytes_in_flight;
    {
        if ! lost_packet.ack_only {
            bytes_in_flight := safe_sub_uint64(bytes_in_flight, lost_packet.size as uint64);
            print("[DEBUG DFY] packet lost bytes_in_flight: ", bytes_in_flight, "\n");
        }
    }

    method onPacketSent (packet: sent_packet_fixed, sent_bytes: uint32)
        requires Valid();
        modifies this`time_of_last_sent_ack_eliciting_packet,
            this`bytes_in_flight;
        modifies sent_packets, sent_packets.Repr;
        ensures fresh(sent_packets.Repr - old(sent_packets.Repr));
        ensures Valid();
    {
        var packet_number := packet.packet_number;
        print("[DEBUG DFY] prepared packet pn=", packet_number, " sent_bytes=", sent_bytes, "\n");
        
        if packet.pn_space != APPLICATION_SPACE {
            return;
        }

        time_of_last_sent_ack_eliciting_packet := packet.sent_time;
        sent_packets.InsertHead(packet); 

        OnPacketSentCC(packet); 
    }

    method OnAckReceived(packet: sent_packet_fixed, ack_eliciting: bool, ack_delay: uint64)
        requires Valid();
        modifies this`largest_acked_packet,
            this`latest_rtt,
            this`min_rtt,
            this`rttvar,
            this`smoothed_rtt;
        ensures Valid();
    {
        var packet_number := packet.packet_number;

        if  largest_acked_packet == UINT62_MAX as uint62 {
            largest_acked_packet := packet_number;
        } else {
            largest_acked_packet := maxu64(largest_acked_packet, packet_number);
        }

        var now := get_system_time();

        // If the largest acknowledged is newly acked and at least one ack-eliciting was newly acked, update the RTT.
        if (ack_eliciting) {
            var latest_rtt := safe_sub_uint64(now, packet.sent_time);
            UpdateRtt(latest_rtt, ack_delay);
        } 
    }

    method CongestionEvent(sent_time: uint64)
        requires Valid();
        modifies this`congestion_recovery_start_time, this`congestion_window, this`ssthresh;
        ensures Valid();
    {
        // Start a new congestion event if packet was sent after the
        // start of the previous congestion recovery period.
        print("[DEBUG DFY] congestion detected\n");
    }

    method under_cc_limit() returns (x: bool)
    {
        x := bytes_in_flight < congestion_window;
    }

    // Enable the ping timer
    method enable_ping_timer()
        requires Valid();
        ensures Valid();
    {
        set_periodic_timer(ping_alarm, 1000); 
    }
}
}
