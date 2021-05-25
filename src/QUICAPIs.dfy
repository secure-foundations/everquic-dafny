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
include "QUICEngine.dfy"

include "HandleFFIs.dfy"
include "QStream.dfy"
include "QStreamManager.dfy"
include "QLossRecovery.dfy"
include "QPacketSpace.dfy"
include "QConnection.dfy"
include "Extern.dfy"

module QUICAPIs {

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
import opened PrivateDLL
import opened QUICEngine

import opened HandleFFIs
import opened QStream
import opened QStreamManager
import opened QLossRecovery
import opened QPacketSpace
import opened QConnection
import opened Extern

class QUICAPI {

//  Public API:  Initialize the QUIC client code. returns engine
static method QUIC_init_server (hostname:string, cbstate:voidptr, cil:cil_t) returns (x: Pointer<engine>)
    ensures x != null && engine_valid(x[0]);
{
    var x1 := initialize_engine(hostname, false, cbstate, cil);
    x := newArrayFill(1, x1);
}

//  Public API:  Initialize the QUIC client code. returns engine
static method QUIC_init_client (hostname:string, cil:cil_t) returns (x: Pointer<engine>)
    ensures x != null && engine_valid(x[0]);
{
    var eng := initialize_engine(hostname, true, null, cil);

    var local_cid := generate_connection_id(20);

    var cs := initialize_connection(hostname, true, local_cid, local_cid);
    eng.connections.InsertHead(cs);

    x := newArrayFill(1, eng);
}

static method setup_initial_crypto_frame(cs: connection)
    returns (ctx: quic_process_ctx)

    requires cs.Valid();

    modifies cs`cstate;

    ensures && ctx.output != null
        && ctx.output.Length == ctx.output_len as int
        && ctx.output_len != 0;
    ensures cs.Valid();
{
    var outbuf_max_len := cs.peer_max_packet_size;
    var outbuf := new byte[outbuf_max_len];

    ctx := new quic_process_ctx([], 0, outbuf, outbuf_max_len as uint64);
    var result := ffi_mitls_quic_process(cs.mitls_state, ctx, 0, UINT32_MAX);

    if result == 0 {
        fatal("FFI_mitls_quic_process failed");
    }

    var bReadKeyChanged := ctx.cur_reader_key != cs.mitls_reader_key ;
    var bWriteKeyChanged := ctx.cur_writer_key != cs.mitls_writer_key;

    if bReadKeyChanged || bWriteKeyChanged {
        fatal("unexpeted key change");
    }

    if ctx.output_len == 0 {
        fatal("output_len can't be 0 here!");
    }

    cs.cstate := Running;
}

// Public API:    Initiate the TLS handshake from client to server.
static method QUIC_handshake (cs: connection) returns (x:bool)
    requires cs.Valid();
    modifies cs`cstate, cs`ready;

    modifies cs.stream_manager`segment_nodes_repr;
    modifies cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr;

    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures cs.Valid();
{
    if cs.cstate != Start {
        return false;
    }

    cs.enter_monitor();
    var ctx := setup_initial_crypto_frame(cs);
    cs.exit_monitor();

    if  ctx.output_len > UINT32_MAX as uint64 {
        fatal("very large output_len");
    }

    cs.send_crypto_frame(ctx.output, ctx.output_len as uint32);

    cs.handshake_complete_wait();

    return true;
}

/* Public API:    Set the maximum stream ID.    It supports setting both UNI and BIDI streams.
            If it is called ahead of the handshake, it influences the initial transport_parameters block.
            Otherwise, it sends updated data via frames. */
static method QUIC_set_max_streams(cs: connection, bidi: bool, max_streams: uint62)
    requires cs.Valid();

    modifies cs`cstate, cs`ready;

    modifies cs.stream_manager`local_max_streams_bidi,
        cs.stream_manager`local_max_streams_uni;

    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    ensures cs.Valid();
{
    cs.enter_monitor();
    var handle := set_max_streams(cs, bidi, max_streams);
    cs.exit_monitor();

    wait_and_close(handle);
}

/* Public API:    Set the maximum data size
    If it is called ahead of the handshake, it influences the initial transport_parameters block.
    Otherwise, it sends updated data via frames. */

static method QUIC_set_max_data (cs: connection, maxdata:uint62)
    requires cs.Valid();

    modifies cs`cstate, cs`ready;
    modifies cs.stream_manager`local_max_data;

    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    ensures cs.Valid();
{
    cs.enter_monitor();
    var handle := set_max_data(cs, maxdata);
    cs.exit_monitor();
    wait_and_close(handle);
}

// (* Public API: Reset a stream *)
static method QUIC_reset_stream (cs: connection, stream: quic_stream_mutable, err:uint16)
    requires cs.Valid();
    requires cs.stream_manager.stream_in_manager(stream);

    modifies cs`ready;
    modifies cs.stream_manager.quic_streams_repr;
    modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

    ensures cs.Valid();
{
    cs.enter_monitor();
    stream.send_state := SendStreamResetSent;
    var frame := create_RESET_STREAM_frame(stream, err);
    var handle := cs.enqueue_fixed_frame(frame);
    cs.update_send_data_ready();
    cs.exit_monitor();

    wait_and_close(handle);
}

// Public API: Close the connection
static method QUIC_close_client (cs: connection)
    requires cs.Valid();

    modifies cs`ready;
    modifies cs`cstate;
    modifies cs.fixedframes, cs.fixedframes.buffer;

    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);
    ensures cs.Valid();
{
    cs.enter_monitor();
    cs.cstate := Closed;
    set_event_handle(engine_send_data_ready());
    cs.exit_monitor();
}

static method QUIC_close_server(cs: connection)
    requires cs.Valid();

    modifies cs`ready;
    modifies cs`cstate;

    ensures cs.Valid();
{
    cs.enter_monitor();
    cs.cstate := Closed;
    set_event_handle(engine_send_data_ready());
    cs.exit_monitor();
}

// Public API: Open a QUIC stream.  Returns NULL on failure.
static method QUIC_open_stream(cs:connection, stream_id:stream_id_t) returns (x:quic_stream_mutable?)
    requires cs.Valid();

    modifies cs.stream_manager`local_streams_uni,
        cs.stream_manager`local_streams_bidi;
    modifies cs.stream_manager`segment_nodes_repr,
        cs.stream_manager`segment_lists_repr,
        cs.stream_manager`quic_streams_repr,
        cs.stream_manager`stream_nodes_repr;
    modifies cs.stream_manager.stream_lists_repr,  cs.stream_manager.stream_nodes_repr;

    ensures cs.Valid();
    ensures x != null ==> x in cs.stream_manager.quic_streams_repr;
{
    cs.enter_monitor();
    x := cs.stream_manager.open_stream_local_initiated_impl(stream_id);
    cs.exit_monitor();
}

// Public API: Send data on a stream.  This blocks until the data has been sent and ACK'd, then returns.  The caller is then able to free the data buffer.
static method QUIC_send_stream(cs:connection, stream: quic_stream_mutable, data:buffer_t, datalength:uint32, fin:bool)  returns (x:Err<bool>)
    requires cs.Valid();
    requires data != null && data.Length == datalength as int;
    requires cs.stream_manager.stream_in_manager(stream);

    modifies cs`ready;
    modifies cs.stream_manager`segment_nodes_repr;
    modifies cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr;

    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures cs.Valid();
{
    if cs.cstate == Closed {
        print("[WARN DFY] send stream connection closed\n");
        return Fail("connection is closed");
    }

    // Validate that the stream ID is either bidi or uni and we are the client
    var stream_id := stream.stream_id;

    if isStreamBidi(stream_id) || isStreamClientInitiated(stream_id) == cs.cf_state.is_client {
        var _ := cs.send_stream_data_async(stream, data, datalength, fin);
        return Ok(true);
    } else {
        print("[WARN DFY] SendStream  direction invalid\n");
        return Fail("Invalid direction for SendStream");
    }
}

// Public API: Receive data on a stream.  This will block until data arrives.  It returns the number of bytes written into the buffer.
static method QUIC_recv_stream (cs:connection) returns (x:stream_recv)
    requires cs.Valid();

    modifies cs.stream_manager.stream_lists_repr,
        cs.stream_manager.stream_nodes_repr,
        cs.stream_manager.quic_streams_repr,
        cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr;

    modifies cs.stream_manager`stream_nodes_repr,
        cs.stream_manager`segment_nodes_repr;

    ensures fresh(cs.stream_manager.stream_nodes_repr - old(cs.stream_manager.stream_nodes_repr))
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))

    ensures cs.Valid();
{
    cs.stream_manager.wait_on_connection_receive_data_ready();

    cs.enter_monitor();
    // Get the first ready stream
    if cs.cstate != Running {
        x := ConnectionError(cs.closedReason);
    } else {
        var is_empty := cs.stream_manager.ready_streams.IsEmpty();
        if is_empty { fatal("ready stream should not be empty"); }
        x := cs.stream_manager.process_receive_ready_streams();
    }
    cs.exit_monitor();

    cs.stream_manager.update_connection_receive_data_ready();
}

// Public API: Close a stream
static method QUIC_close_stream (cs: connection, stream: quic_stream_mutable)
    requires cs.Valid();
    requires cs.stream_manager.stream_in_manager(stream);
    modifies cs.stream_manager.quic_streams_repr;
    ensures cs.Valid();
{
    cs.enter_monitor();
    close_stream_internal(stream);
    cs.exit_monitor();
}

// Public API:  Query if the 'fin' marker has been received, for end of the stream
static method QUIC_stream_fin (cs: connection, stream: quic_stream_mutable) returns (x:bool)
    requires cs.Valid();
    requires cs.stream_manager.stream_in_manager(stream);
{
    cs.enter_monitor();
    x := stream.recv_state == RecvStreamDataRead;
    cs.exit_monitor();
}


//  Public API:    Get the associated application state for this connection
static method QUIC_get_app_state (cs: connection) returns (x : voidptr)
    requires cs.Valid();
{
    x := cs.app_state;
}

//  Public API:    Set the associated application state for this connection, returning the previous value
static method QUIC_set_app_state (cs: connection, new_state:voidptr) returns (x: voidptr)
    requires cs.Valid();
    modifies cs`app_state;
    ensures cs.Valid();
{
    cs.enter_monitor();
    var old_state := cs.app_state;
    cs.app_state := new_state;
    cs.exit_monitor();
    return old_state;
}

/* Public API: Get the 0-rtt ticket.    This may return null immediately after the
        handshake completes, then later become non-null.    The caller should retry
        periodically until a non-null return value */
static method QUIC_get_ticket (cs: connection) returns (x: Pointer<mitls_ticket>)
    requires cs.Valid();
{
    x := cs.tls_ticket;
}

// * Public API: Set the 0-rtt ticket.    This must be called before QUIC_handshake()
static method QUIC_set_ticket (cs: connection, ticket:Pointer<mitls_ticket>)
    requires cs.Valid();
    modifies cs`tls_ticket;
    ensures cs.Valid();
{
    cs.tls_ticket := ticket;
}

//  Public API:  Return the one connection pointer stored inside a client engine instance
static method QUIC_get_client (eng_ptr:Pointer<engine>) returns (x : connection?)
    requires eng_ptr != null && engine_valid(eng_ptr[0]);
    requires eng_ptr[0].eis_client && |eng_ptr[0].connections.Vals| != 0;
{
    var eng := eng_ptr[0];
    x := eng.connections.PeekHead();
}

static method QUIC_get_connection_id(eng_ptr:Pointer<engine>, packet:buffer_t, packet_len:uint32)
    returns (x :Err<connection_id_fixed>)
    requires eng_ptr != null && engine_valid(eng_ptr[0]);
    requires buffer_valid(packet, packet_len);
{
    x := decode_dcid(packet, packet_len); 
}

// Public API: Process a received packet.    Returns 0xffffffff if there is an error.
static method QUIC_process_packet (
        eng:engine,
        ghost gcs: connection?,
        cid: connection_id_fixed,
        packet:buffer_t,
        packet_len:uint32)
    returns (x :uint32)

    requires engine_valid(eng);
    requires buffer_valid(packet, packet_len);
    requires gcs == ghost_get_connection_from_cs(eng.connections.Vals, cid);

    modifies packet;
    modifies eng.connections, eng.connections.Repr;

    modifies if gcs == null then null else gcs;
    modifies if gcs == null then null else gcs.fixedframes;
    modifies if gcs == null then null else gcs.fixedframes.buffer;
    modifies if gcs == null then null else gcs.lrcc_manager;
    modifies if gcs == null then null else gcs.lrcc_manager.sent_packets;
    modifies if gcs == null then {} else gcs.lrcc_manager.sent_packets.Repr;
    modifies if gcs == null then null else gcs.short_header_packets;
    modifies if gcs == null then null else gcs.short_header_packets.buffer;
    modifies if gcs == null then null else gcs.pspace_manager;
    modifies if gcs == null then {} else gcs.pspace_manager.ps_states_repr;
    modifies if gcs == null then {} else gcs.pspace_manager.ack_buffers_repr;
    modifies if gcs == null then {} else gcs.pspace_manager.crypto_states_repr;
    modifies if gcs == null then null else gcs.stream_manager;
    modifies if gcs == null then {} else gcs.stream_manager.segment_nodes_repr;
    modifies if gcs == null then {} else gcs.stream_manager.segment_lists_repr;
    modifies if gcs == null then {} else gcs.stream_manager.quic_streams_repr;
    modifies if gcs == null then {} else gcs.stream_manager.stream_lists_repr;
    modifies if gcs == null then {} else gcs.stream_manager.stream_nodes_repr;

    ensures engine_valid(eng);
{
    var temp_0 := decode_dcid(packet, packet_len);
    if temp_0.Fail? { return 0xffffffff; }
    var dcid := temp_0.value;

    if !cid_equal(dcid, cid) {
        fatal("expect cid to be from this packet!!");
    }

    var cs := get_connection(eng, cid);
    assert cs == gcs;

    var temp_1 := engine_process_packet(eng, cs, dcid, packet, packet_len);

    assert engine_valid(eng);
    if temp_1.Fail? { return 0xffffffff; }
    return 0;
}

/*  Public API:  Prepare a new packet for transmission.  The packet is an OUT buffer of
     length packetlen.  The return value is the number of bytes of data present in then
     packet buffer. This API blocks (non-alertable) until a new packet is ready for
     transmission. */
static method QUIC_prepare_packet (eng:engine, packet:buffer_t, packet_len:uint32, ghost gcs: connection)
    returns (x: api_prepare_result)
    requires engine_valid(eng);
    requires buffer_valid(packet, packet_len);

    requires gcs == ghost_find_ready_connection_from_cs(eng.connections.Vals);

    modifies gcs`cstate, gcs`ready;

    modifies gcs.stream_manager`segment_nodes_repr,
        gcs.stream_manager`total_data_sent;

    modifies gcs.stream_manager.quic_streams_repr,
        gcs.stream_manager.segment_nodes_repr,
        gcs.stream_manager.segment_lists_repr;

    modifies gcs.fixedframes,
        gcs.fixedframes.buffer;

    modifies gcs.lrcc_manager`time_of_last_sent_ack_eliciting_packet,
        gcs.lrcc_manager`bytes_in_flight;

    modifies gcs.lrcc_manager.sent_packets, gcs.lrcc_manager.sent_packets.Repr;

    modifies gcs.pspace_manager.ps_states_repr,
        gcs.pspace_manager.crypto_states_repr;

    modifies packet;

    ensures engine_valid(eng);
{
    print("[DEBUG DFY] start waiting engine_send_data_ready\n");
    wait_for_event_handle (engine_send_data_ready(), 0xffffffff);
    print("[DEBUG DFY] done waiting engine_send_data_ready\n");

    monitor_enter (eng.emonitor);
    var cs := find_ready_connection(eng);
    if cs == null { fatal("no ready to send connection!!!"); }

    assert cs == gcs;
    var packet_op;

    if (cs.cstate != Running) {
        print("[DEBUG DFY] prepare packet when connection is not running\n");
        x := api_prepare_result(PREPARE_ERROR_CLOSED, 0);
    } else {
        packet_op := engine_prepare_packet(eng, cs, packet, packet_len); 

        if packet_op.Fail? {
            x := api_prepare_result(PREPARE_ERROR_OTHER, 0);
        } else {
            x := api_prepare_result(PREPARE_SUCCESS, packet_op.value.0);
        }
    }
    monitor_exit (eng.emonitor);
}

}

}
