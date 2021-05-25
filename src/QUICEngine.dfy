/*
QUIC Engine - the top-level API for QUIC clients and servers

@summary:  Top-level QUIC API

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
include "QUICConnection.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "HandleFFIs.dfy"
include "PrivateDLL.dfy"

include "QStream.dfy"
include "QStreamManager.dfy"
include "QLossRecovery.dfy"
include "QConnection.dfy"
include "Extern.dfy"

module QUICEngine
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
import opened QUICConnection
import opened QUICDataTypes
import opened QUICConstants
import opened HandleFFIs
import opened QStream
import opened QStreamManager
import opened QLossRecovery
import opened QConnection
import opened Extern
import opened PrivateDLL

method initialize_engine(hostname:string, is_client:bool, cbstate:voidptr, cil:cil_t) returns (x: engine)
    ensures engine_valid(x);
    ensures fresh(x.connections)
        && fresh(x.connections.Repr)
        && fresh(x.versionreplies)
        && fresh(x.versionreplies.Repr);
{
    var emonitor := monitor_init();
    var connections := new connectionholder_list();
    var versionreplies := new versionreply_list();

    x := engine(is_client, emonitor, hostname, connections, versionreplies, cbstate, cil);
}

function ghost_find_ready_connection_from_cs(cs:seq<connection>) : (c:connection?)
    reads cs;
    ensures c != null ==> c in cs && c.ready;
{
    if |cs| == 0 then (null) else (
        if cs[0].ready then cs[0] else (
        ghost_find_ready_connection_from_cs(cs[1..])
        )
    )
}

method find_ready_connection_from_cs(ch:connectionholder_list, it:DllIterator<connection>)
    returns (c:connection?)
    requires ch.Valid();
    requires it.Valid();
    requires it.d == ch;
    modifies it;
    ensures old(it.GetIndex()) < |ch.Vals|;
    ensures c == ghost_find_ready_connection_from_cs(ch.Vals[old(it.GetIndex())..]);
    decreases |ch.Vals| - it.GetIndex(), it.Valid();
{
    var cs := it.GetVal();
    if cs.ready {
        return cs;
    } else {
        var continue := it.MoveNext();
        if continue {
            c := find_ready_connection_from_cs(ch, it);
        } else {
            c := null;
        }
    }
}

method find_ready_connection(eng: engine) returns (x: connection?)
    requires engine_valid(eng);
    ensures x != null ==> x.Valid();
    ensures x == ghost_find_ready_connection_from_cs(eng.connections.Vals);
{
    var connections := eng.connections;

    var is_empty := connections.IsEmpty();
    if is_empty { return null; }

    var iter := new DllIterator(connections);
    x := find_ready_connection_from_cs(connections, iter);
}

method {:timeLimit 480} engine_prepare_packet(eng: engine, cs: connection, packet:buffer_t, packet_len:uint32)
    returns (x: Err <(uint32, voidptr)>)
    requires engine_valid(eng);
    requires buffer_valid(packet, packet_len);

    requires cs == ghost_find_ready_connection_from_cs(eng.connections.Vals);

    modifies cs`cstate, cs`ready;

    modifies cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`total_data_sent;

    modifies cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;

    modifies cs.fixedframes,
        cs.fixedframes.buffer;

    modifies cs.lrcc_manager`time_of_last_sent_ack_eliciting_packet,
        cs.lrcc_manager`bytes_in_flight;

    modifies cs.lrcc_manager.sent_packets, cs.lrcc_manager.sent_packets.Repr;

    modifies cs.pspace_manager.ps_states_repr,
        cs.pspace_manager.crypto_states_repr;

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures fresh(cs.lrcc_manager.sent_packets.Repr - old(cs.lrcc_manager.sent_packets.Repr));

    modifies packet;

    ensures && eng.connections.Valid()
        && (forall c :: c in eng.connections.Vals ==> c.Valid())
        && (forall i, j :: 0 <= i < j < |eng.connections.Vals| ==>
            connection_disjoint(eng.connections.Vals[i], eng.connections.Vals[j]))
    ensures engine_valid(eng);
{
    var temp_0 := connnection_prepare_packet (cs, packet, packet_len);
    if temp_0.Fail? {return Fail(temp_0.err);}
    var result := temp_0.value;

    return Ok((result, cs.app_state));
}

method engine_version_reply(eng: engine, packet:buffer_t, packet_len:uint32)
    returns (x: Err <(uint32, voidptr)>)

    requires buffer_valid(packet, packet_len);
    requires engine_valid(eng);

    modifies eng.versionreplies, eng.versionreplies.Repr;
    modifies packet;

    ensures engine_valid(eng);
{
    fatal("version reply not supported");
}

function ghost_get_connection_from_cs(cs: seq<connection>, cid:connection_id_fixed) : (c:connection?)
    reads cs;
    ensures c != null ==> c in cs && cid_equal(c.src_connection_id, cid);
{
    if |cs| == 0 then (null) else (
        if cs[0].src_connection_id == cid then cs[0] else (
        ghost_get_connection_from_cs(cs[1..], cid)
        )
    )
}

method get_connection_from_cs(ch:connectionholder_list, cid:connection_id_fixed, it:DllIterator<connection>)
    returns (c:connection?)
    requires ch.Valid();
    requires it.Valid();
    requires it.d == ch;
    modifies it;
    ensures old(it.GetIndex()) < |ch.Vals|;
    ensures c == ghost_get_connection_from_cs(ch.Vals[old(it.GetIndex())..], cid);
    decreases |ch.Vals| - it.GetIndex(), it.Valid();
{
    var cs := it.GetVal();
    var found := cid_equal(cs.src_connection_id, cid);
    if found {
        return cs;
    }
    var continue := it.MoveNext();
    if continue {
        c := get_connection_from_cs(ch, cid, it);
    } else {
        c := null;
    }
}

// (** Determines a connection given a destination connection ID value, or returns NULL if there is no match. *)
method get_connection(eng: engine, cid: connection_id_fixed) returns (c :connection?)
    requires engine_valid(eng);
    ensures c != null ==> c.Valid();
    ensures c == ghost_get_connection_from_cs(eng.connections.Vals, cid);
{
    monitor_enter (eng.emonitor);

    var empty := eng.connections.IsEmpty();
    if empty {
        c := null;
    } else {
        var iter := new DllIterator(eng.connections);
        c := get_connection_from_cs(eng.connections, cid, iter);
    }

    monitor_exit(eng.emonitor);

    if c == null {
        print("[DEBUG DFY] get_connection_from_id: connection not found!\n");
    }
}

/* Read the dest connectionID from a header (long or short form) and either return
        the associated connection pointer, or null if there is no match */

method decode_dcid(packet:buffer_t, packet_len:uint32) returns (x :Err<connection_id_fixed>)
    requires buffer_valid(packet, packet_len);
{
    var temp;
    if is_long_header_packet(packet[0]) { // long header
        temp := decode_connection_id(packet, packet_len, 5);
    } else { // short header
        temp := parse_connection_id(packet, packet_len, 1, ENGINE_CIL);
    }
    if temp.Fail? { return Fail("[ERROR] failed to get cid"); }
    return Ok(temp.value.0);
}

method server_create_new_connection(eng: engine,
        scid: connection_id_fixed,
        dcid: connection_id_fixed,
        packet:buffer_t,
        packet_len:uint32)
    returns (cs: connection)

    requires buffer_valid(packet, packet_len);

    modifies packet;

    ensures cs.Valid();
    ensures && fresh(cs)
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
    cs := initialize_connection(eng.ehostname, false, scid, dcid);
    var offset_op := process_client_initial_packet_impl(cs, dcid, packet, packet_len);
    cs.app_state := newconnection_FFI(eng.newconnection_state, cs);
}

method process_client_initial_packet(
        eng: engine,
        scid: connection_id_fixed,
        dcid: connection_id_fixed,
        packet:buffer_t,
        packet_len:uint32)
    returns (x :Err<uint32>)

    requires engine_valid(eng);
    requires buffer_valid(packet, packet_len);

    modifies packet;
    modifies eng.connections, eng.connections.Repr;

    ensures fresh(eng.connections.Repr - old(eng.connections.Repr));
    ensures engine_valid(eng);
{
    monitor_enter (eng.emonitor);
    var cs := server_create_new_connection(eng, scid, dcid, packet, packet_len);
    eng.connections.InsertHead(cs);
    print("[DEBUG DFY] new connection added to engine\n");
    monitor_exit (eng.emonitor);
}

// (** respond to a client's request for version nego by queuing a nego packet for transmission *)
method negotiateVersion (eng: engine, cid:connection_id_fixed)
{
    fatal("[ERROR] not supporting version negotiation for now");
    print("[DEBUG DFY] negotiateVersion\n");

    var cs: connection? := null;
    var appstate := newconnection_FFI(eng.newconnection_state, cs);
    var v := versionreply_fixed(cid, appstate);

    monitor_enter (eng.emonitor);
    eng.versionreplies.InsertTail(v);
    set_event_handle (engine_send_data_ready());
    monitor_exit (eng.emonitor);
}

method engine_process_initial_packet(eng: engine, packet:buffer_t, packet_len:uint32)
    returns (x: Err<uint32>)
    requires engine_valid(eng);
    requires buffer_valid(packet, packet_len);

    modifies packet;
    modifies eng.connections, eng.connections.Repr;

    ensures fresh(eng.connections.Repr - old(eng.connections.Repr));
    ensures engine_valid(eng);
{
    var packet_type := get_packet_type(packet[0]);

    if !eng.eis_client && packet_type == INITIAL_TYPE  {
        
        print("[DEBUG DFY]: server parsing initial packet\n");

        var temp_0 := decode_client_initial_packet_partial(packet, packet_len);
        if temp_0.Fail? {
            print("[WARN DFY]: server failed to parse inital packet\n");
            return Fail("failed to decode scid from client initial packet");
        }
        var scid, dcid, version := temp_0.value.0, temp_0.value.1, temp_0.value.2;

        var temp_1 := process_client_initial_packet(eng, scid, dcid, packet, packet_len);
        if temp_1.Fail? { return Fail("failed to decrypt client inital packet"); }
        return Ok(0);
    }

    print("[WARN DFY]: sever unexpected connectionid in short packet\n");
    return Fail("unexpected connectionid in short packet");
}

method {:timeLimit 600} engine_prcoess_packet(eng: engine, cs: connection, ghost gcid: connection_id_fixed, packet:buffer_t, packet_len:uint32)
    returns (x: Err<uint32>)

    requires engine_valid(eng);
    requires buffer_valid(packet, packet_len);
    requires cs == ghost_get_connection_from_cs(eng.connections.Vals, gcid);

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

    ensures && eng.connections.Valid()
        && (forall c :: c in eng.connections.Vals ==> c.Valid())
        && (forall i, j :: 0 <= i < j < |eng.connections.Vals| ==>
            connection_disjoint(eng.connections.Vals[i], eng.connections.Vals[j]))
{
    x := connection_process_packet(cs, packet, packet_len);
}

method engine_process_packet(eng: engine, cs: connection?, ghost gcid: connection_id_fixed, packet:buffer_t, packet_len:uint32) returns (x :Err<uint32>)
    requires buffer_valid(packet, packet_len);
    requires engine_valid(eng);
    requires cs == ghost_get_connection_from_cs(eng.connections.Vals, gcid);

    modifies packet;
    modifies eng.connections, eng.connections.Repr;

    requires cs != null ==> cs.Valid();

    modifies if cs == null then null else cs;
    modifies if cs == null then null else cs.stream_manager;
    modifies if cs == null then null else cs.fixedframes;
    modifies if cs == null then null else cs.fixedframes.buffer;
    modifies if cs == null then null else cs.lrcc_manager;
    modifies if cs == null then null else cs.lrcc_manager.sent_packets;
    modifies if cs == null then {} else cs.lrcc_manager.sent_packets.Repr;
    modifies if cs == null then null else cs.short_header_packets;
    modifies if cs == null then null else cs.short_header_packets.buffer;
    modifies if cs == null then null else cs.pspace_manager;
    modifies if cs == null then {} else cs.pspace_manager.ps_states_repr;
    modifies if cs == null then {} else cs.pspace_manager.ack_buffers_repr;
    modifies if cs == null then {} else cs.pspace_manager.crypto_states_repr;
    modifies if cs == null then null else cs.stream_manager;
    modifies if cs == null then {} else cs.stream_manager.segment_nodes_repr;
    modifies if cs == null then {} else cs.stream_manager.segment_lists_repr;
    modifies if cs == null then {} else cs.stream_manager.quic_streams_repr;
    modifies if cs == null then {} else cs.stream_manager.stream_lists_repr;
    modifies if cs == null then {} else cs.stream_manager.stream_nodes_repr;

    ensures engine_valid(eng);
{
    if  cs == null {
        if ! eng.eis_client {
            print("[DEBUG DFY] server received first initial packet\n");
            x := engine_process_initial_packet(eng, packet, packet_len);
        } else {
            print("[WARN DFY]: client dropping spurious packet\n");
        }
    } else {
        print("[DEBUG DFY] received packet on an existing connection\n");
        if cs.cstate == Closed {
            print("[DEBUG DFY] received packet on an closed connection\n");
            return Ok(0);
        }
        x := engine_prcoess_packet(eng, cs, gcid, packet, packet_len);
    }
}

}
