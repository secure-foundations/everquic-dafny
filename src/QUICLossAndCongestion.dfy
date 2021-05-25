include "Options.dfy"
include "NativeTypes.dfy"
include "QEngine.dfy"
include "QUICUtils.dfy"
include "QUICTLS.dfy"
include "QUICFFI.dfy"
include "QUICStream.dfy"
include "Misc.dfy"
include "OverFlowCheck.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "PrivateDLL.dfy"
include "HandleFFIs.dfy"

include "QStream.dfy"
include "QStreamManager.dfy"
include "QLossRecovery.dfy"
include "QConnection.dfy"
include "Extern.dfy"
/*
QUIC Loss and Congestion Control

@summary: Implement loss detection and congestion control on the network
*/

module QUICLossAndCongestion {

import opened Options
import opened NativeTypes
import opened QEngine
import opened QUICUtils
import opened QUICTLS
import opened QUICFFI
import opened QUICStream
import opened Misc
import opened OverFlowCheck
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


// Alarm callback, when the loss-timer fires.
method onLossDetectionAlarm (ignore1:voidptr, cs: connection, ignore2:voidptr)
    requires cs.Valid();
    modifies cs`ready;
    modifies cs.lrcc_manager`loss_time,
        cs.lrcc_manager`bytes_in_flight,
        cs.lrcc_manager`congestion_window,
        cs.lrcc_manager`ssthresh,
        cs.lrcc_manager`congestion_recovery_start_time;

    modifies cs.lrcc_manager.sent_packets, cs.lrcc_manager.sent_packets.Repr;
    modifies cs.stream_manager`segment_nodes_repr, cs.stream_manager`total_data_sent;
    modifies cs.fixedframes, cs.fixedframes.buffer;
        ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    modifies cs.stream_manager.quic_streams_repr, cs.stream_manager.segment_nodes_repr, cs.stream_manager.segment_lists_repr;
    modifies cs.pspace_manager.ps_states_repr, cs.pspace_manager.ack_buffers_repr;
    ensures cs.Valid();
{
    monitor_enter(cs.cf_state.monitor);
    print("[DEBUG DFY] loss detection alarm\n");

    cs.handle_loss_packets();
    cs.update_send_data_ready();

    monitor_exit(cs.cf_state.monitor);
}

//  Ping callback, when the ping-timer fires.  This may cause a ping packet to be transmitted, to keep the connection alive.
method onPingAlarm (ignore1:voidptr, cs: connection, ignore2:voidptr)

  requires cs.Valid();
  modifies cs`ready;
  modifies cs.pspace_manager.ps_states_repr;
  modifies cs`pingPending;
  ensures cs.Valid();

{
    monitor_enter(cs.cf_state.monitor);
    cs.pspace_manager.enable_ack_only_packet(APPLICATION_SPACE);
    cs.update_send_data_ready();
    monitor_exit(cs.cf_state.monitor);
}

}
