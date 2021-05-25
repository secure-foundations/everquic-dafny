include "Options.dfy"
include "NativeTypes.dfy"
include "PrivateDLL.dfy"
include "QEngine.dfy"
include "QUICUtils.dfy"
include "QUICTLS.dfy"
include "QUICFFI.dfy"
include "Misc.dfy"
include "OverFlowCheck.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"

include "HandleFFIs.dfy"
include "QStream.dfy"
include "QStreamManager.dfy"
include "QConnection.dfy"
include "Extern.dfy"
/*

QUIC Stream - the high-level stream interface for applications

@summary: streams within a QUIC connection
*/
module QUICStream {
import opened Options
import opened NativeTypes
import opened QEngine
import opened QUICUtils
import opened QUICTLS
import opened QUICFFI
import opened Misc
import opened OverFlowCheck
import opened PrivateDLL
import opened QUICDataTypes
import opened QUICConstants
import opened HandleFFIs
import opened QStream
import opened QConnection
import opened Extern

// Enqueue a CONNECTION_CLOSE.  This isn't waitable, as no response is expected from the peer
method enqueueConnectionClose(cs:connection, errcode:uint16)

  requires cs.Valid();
  modifies cs`ready;
  modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

  ensures cs.Valid();

{
    var data := new byte[4];
    var offset := append8(data, 0, CONNECTION_CLOSE_APP_TYPE); // from application
    offset := append16(data, offset, errcode); // Error Code
    offset := append8(data, offset, 0x00); // Reason Phrase Length (0)
    var frame := fixed_frame_raw(data[..], offset, NONE_HANDLE);
    cs.fixedframes.push_back(frame);
    cs.update_send_data_ready();
}

// Abort a connection:  send a CONNECTION_CLOSE and halt further communication
method abortConnection(cs:connection, transportErrorCode:uint16)

  requires cs.Valid();
  modifies cs`ready;
  modifies cs.fixedframes, cs.fixedframes.buffer;
    ensures cs.fixedframes.buffer == old(cs.fixedframes.buffer) || fresh(cs.fixedframes.buffer);

  ensures cs.Valid();
{
    enqueueConnectionClose(cs, transportErrorCode);
}

// I'm not moving this into class, because we might want to remove the stream from connection
method close_stream_internal(stream: quic_stream_mutable)
    requires stream.Valid();
    modifies stream`recv_state;
    modifies stream`send_state;
    modifies stream`error_code;
    ensures stream.Valid();
{
    stream.recv_state := RecvStreamResetRead;
    stream.send_state := SendStreamResetRecvd;
    stream.error_code := 0;
}

method mitls_process_crypto(cs: connection, inbuf_cur: seq<byte>, input_len: uint32, ghost prev_output_len: uint32)
    returns (ctx: quic_process_ctx)
    ensures && ctx.output_len as int <= UINT32_MAX as int
        && ctx.output != null
        && ctx.output.Length == ctx.output_len as int
        && ctx.consumed_bytes as int <= input_len as int
        && ctx.output_len as int < prev_output_len as int
{
    var outbuf_len := cs.peer_max_packet_size;
    var outbuf := new byte[outbuf_len];

    ctx := new quic_process_ctx(inbuf_cur, input_len as uint64, outbuf, outbuf_len as uint64);
    // for debugging
    ctx.cur_reader_key := cs.mitls_reader_key;
    ctx.cur_writer_key := cs.mitls_writer_key;

    var result := ffi_mitls_quic_process(cs.mitls_state, ctx, 0, prev_output_len);

    if result == 0 { fatal("FFI_mitls_quic_process failed"); }
    if ctx.to_be_written != 0 { fatal("insufficient buffer to hold handshake data"); }
}

method update_keys(cs: connection, ctx: quic_process_ctx, new_epoch: epoch, read_key_changed: bool, write_key_changed: bool)
    requires cs.Valid();
    modifies cs.pspace_manager`crypto_states;
    modifies cs.pspace_manager`crypto_states_repr;
    modifies cs.pspace_manager.ps_states_repr;
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures cs.Valid();
{
    var ps := cs.epoch_to_packet_space(new_epoch);

    print("[DEBUG DFY] attempted key update ", ps_str(ps), "\n");

    if ctx.cur_reader_key == 1 &&  ctx.cur_writer_key == 1 {
        print("[DEBUG DFY] application traffic secret update\n");

        var rk, wk := get_tls_secrets(cs, 1, cs.cf_state.is_client);
        cs.pspace_manager.update_crypto_state(ps, 1, rk, false);
        cs.pspace_manager.update_crypto_state(ps, 1, wk, true);
    }

    if write_key_changed && ctx.cur_writer_key == 0 {
        print("[DEBUG DFY] handshake traffic secret update\n");
        var rk, wk := get_tls_secrets(cs, 0, cs.cf_state.is_client);
        cs.pspace_manager.update_crypto_state(ps, 0, rk, false);
        cs.pspace_manager.update_crypto_state(ps, 0, wk, true);
    }
}

method some_unkown_key_update_process(cs: connection, ctx: quic_process_ctx)
    requires cs.Valid();
    modifies cs`epoch, cs`cstate, cs`mitls_reader_key, cs`mitls_writer_key;
    modifies cs.pspace_manager`crypto_states;
    modifies cs.pspace_manager`crypto_states_repr;
    modifies cs.pspace_manager.ps_states_repr;
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures cs.Valid();
{
    var read_key_changed := ctx.cur_reader_key != cs.mitls_reader_key;
    var write_key_changed := ctx.cur_writer_key != cs.mitls_writer_key;

    cs.mitls_reader_key := ctx.cur_reader_key;
    cs.mitls_writer_key := ctx.cur_writer_key;

    if (read_key_changed || write_key_changed) {
        var newEpoch := cs.update_epoch(read_key_changed);
        cs.cstate := Running;

        update_keys(cs, ctx, newEpoch, read_key_changed, write_key_changed);
    }

    if and16(ctx.flags, qflag_complete) != 0 {
        cs.lrcc_manager.enable_ping_timer();
        set_periodic_timer(cs.lrcc_manager.loss_detection_timer, 10000); 

        if cs.cf_state.is_client {
            set_event_handle (cs.cf_state.handshakeComplete);
            print("[DEBUG DFY] client side handshake completed\n");
        } else {
            print("[DEBUG DFY] server side handshake completed\n");
        }
    }
}

method process_crypto_segment_aux(cs: connection, inbuf_cur: seq<byte>, input_len: uint32, ghost prev_output_len: uint32)
    returns (ctx: quic_process_ctx)

    requires cs.Valid();

    modifies cs.stream_manager`segment_nodes_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))

    modifies cs.stream_manager.segment_nodes_repr, cs.stream_manager.segment_lists_repr, cs.stream_manager.quic_streams_repr;
    modifies cs`epoch, cs`cstate, cs`mitls_reader_key, cs`mitls_writer_key, cs`ready;
    modifies cs.pspace_manager`crypto_states;
    modifies cs.pspace_manager`crypto_states_repr;
    modifies cs.pspace_manager.ps_states_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));

    ensures cs.Valid();
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));
    ensures && ctx.output_len as int <= UINT32_MAX as int
        && ctx.output != null
        && ctx.output.Length == ctx.output_len as int
        && ctx.consumed_bytes as int <= input_len as int
        && ctx.output_len as int < prev_output_len as int
{
    ctx := mitls_process_crypto(cs, inbuf_cur, input_len, prev_output_len);

    var output_len := ctx.output_len;

    if output_len != 0 {
        print("[DEBUG DFY] queuing crypto data ", output_len, "\n");
        cs.send_crypto_frame(ctx.output, output_len as uint32);
    }

    some_unkown_key_update_process(cs, ctx);
}

// data has arrived in a CRYPTO frame.  Forward it to miTLS
method process_crypto_segment(cs:connection, segment: qstream_segment_fixed) returns (x:Err<bool>)
    requires cs.Valid();

    modifies cs.stream_manager`segment_nodes_repr;
    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))

    modifies cs.stream_manager.segment_nodes_repr,
        cs.stream_manager.segment_lists_repr,
        cs.stream_manager.quic_streams_repr;
    modifies cs`epoch, cs`cstate, cs`mitls_reader_key, cs`mitls_writer_key, cs`ready;
    modifies cs.pspace_manager`crypto_states;
    modifies cs.pspace_manager`crypto_states_repr;
    modifies cs.pspace_manager.ps_states_repr;
    ensures fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr));

    ensures fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr));
    ensures cs.Valid();
{
    var finished := false;

    var inbuf_cur_length := segment.datalength;
    var inbuf_cur := segment.data;
    ghost var prev_output_len := UINT32_MAX;

    while ! finished
        decreases inbuf_cur_length, prev_output_len;
        invariant cs.Valid();
        invariant inbuf_cur_length as int == |inbuf_cur|
        invariant fresh(cs.stream_manager.segment_nodes_repr - old(cs.stream_manager.segment_nodes_repr))
        invariant fresh(cs.pspace_manager.crypto_states_repr - old(cs.pspace_manager.crypto_states_repr))
    {
        var ctx := process_crypto_segment_aux(cs, inbuf_cur, inbuf_cur_length, prev_output_len);
        var consumed_bytes := ctx.consumed_bytes as uint32;

        prev_output_len := ctx.output_len as uint32;
    
        inbuf_cur_length := inbuf_cur_length - consumed_bytes;
        inbuf_cur := inbuf_cur[consumed_bytes..];

        // if it takes no more input, and produces no more output
        finished := inbuf_cur_length == 0 && ctx.output_len == 0; 
    }
}
}
