include "Options.dfy"
include "NativeTypes.dfy"
include "QUICDataTypes.dfy"
include "QConnection.dfy"

// QUIC FFI - Calls from QUIC code into miTLS, libquiccrypto, or Windows APIs.
// @summary:  Make calls into Everest and Windows APIs

module QUICFFI {
    import opened Options
    import opened NativeTypes
    import opened QUICDataTypes
    import opened QConnection

    method {:extern "QUICFFI", "ffi_mitls_init"} ffi_mitls_init() returns (i:int32)

    datatype mitls_version =
        | TLS_SSL3
        | TLS_1p0
        | TLS_1p1
        | TLS_1p2
        | TLS_1p3

    datatype mitls_nego_action =
        | TLS_nego_abort
        | TLS_nego_accept
        | TLS_nego_retry

    datatype mitls_extension = mitls_extension (
        ext_datatype: uint16,
        // ext_data: Pointer<byte>,
        ext_data: buffer_t,
        ext_data_len: Pointer<uint64>
    )

  datatype mitls_alpn = mitls_alpn (
    alpn_str: string,
    alpn_str_len: Pointer<uint64>
  )

  datatype quic_config = quic_config (
    is_server: int32,

    alpn: Pointer<mitls_alpn>,
    alpn_count: Pointer<uint64>,
    cipher_suites: string,
    signature_algorithms: string,
    named_groups: string,
    enable_0rtt: int32,

    // only used by the client
    host_name: string,
    server_ticket: Pointer<quic_ticket>,
    exts: Pointer<mitls_extension>,
    exts_count: Pointer<uint64>,

    callback_state: Pointer<connection>, // passed back as the first argument of callbacks, may be null

    // only used by the server
    ticket_enc_alg: voidptr,
    ticket_key: voidptr,
    ticket_key_len: Pointer<uint64>
  )

method {:extern "QUICFFI", "ffi_mitls_find_custom_extension "} ffi_mitls_find_custom_extension (is_server:int32,
        exts:buffer<byte>,
        ext_len:Pointer<uint64>,
        ext_type:uint16,
        ext_data:Pointer<buffer<byte>>,
        ext_data_len:Pointer<uint64>)
    returns (x:int32)

    ensures ext_data != null && ext_data[0] != null;
    ensures ext_data_len != null && 0 <= ext_data_len[0] < 0x100000000;
    ensures ext_data_len[0] as int == ext_data[0].Length;

method {:extern "QUICFFI", "ffi_mitls_quic_create"} ffi_mitls_quic_create(quic_state:Pointer<voidptr>,  cfg:Pointer<quic_config>) returns (x:int32)

const qflag_complete:uint16:=0x01
const qflag_application_key:uint16:=0x02
const qflag_rejected_0rtt:uint16:=0x10

class quic_process_ctx
{
    var input: seq<byte>; // can be NULL, a TLS message fragment read by QUIC
    var input_len: uint64;  // Size of input buffer (can be 0)
    var output: buffer<byte>;  // a buffer to store handshake data to send

    var output_len: uint64;  // In: size of output buffer Out: bytes written to output

    // Outputs:
    var tls_error: uint16; // alert code of a locally-generated TLS alert
    var consumed_bytes: uint64; // how many bytes of the input have been processed - leftover bytes must be processed in the next call
    var to_be_written: uint64; // how many bytes are left to write (after writing *output)
    var tls_error_desc: string; // meaningful description of the local error (actually const char*)

    var cur_reader_key: int32; // current reader epoch, if incremented by TLS, QUIC must switch key BEFORE processing further packets.
    var cur_writer_key: int32; // current writer epoch, if incremented by TLS, QUIC must switch key AFTER writing *output
    var flags: uint16; // Bitfield of return flags (see above)

    constructor(input_buf: seq<byte>, input_len: uint64, output_buf: buffer<byte>, output_len: uint64)
      ensures this.input_len == input_len;
    {
        this.input := input_buf;
        this.input_len := input_len;

        this.output := output_buf;
        this.output_len := output_len;

        this.tls_error := 0;
        this.consumed_bytes := 0;
        this.to_be_written := 0;
        this.tls_error_desc := "";

        this.cur_reader_key := -1;
        this.cur_writer_key := -1;
        this.flags:= 0;
    }
}

method {:extern "QUICFFI", "ffi_mitls_quic_process"} ffi_mitls_quic_process(
  quic_state:voidptr,
  ctx:quic_process_ctx,
  outbuf_offset:uint32,
  ghost prev_output_len: uint32)
  returns (x:int32)

  modifies ctx`output, ctx`output_len, ctx`consumed_bytes;
  ensures x != 0 ==>
  && ctx.output != null
  && ctx.output.Length == ctx.output_len as int
  && ctx.consumed_bytes <= ctx.input_len
  && ctx.output_len as int < prev_output_len as int

method {:extern "QUICFFI", "ffi_mitls_quic_free"} ffi_mitls_quic_free(state:voidptr)

// quic_direction enum
const quicWriter : uint32 := 0
const quicReader : uint32 := 1

method {:extern "QUICFFI", "ffi_mitls_quic_get_record_secrets"} ffi_mitls_quic_get_record_secrets(state:voidptr, client_secret:buffer<byte>, server_secret:buffer<byte>, epoch:int32) returns (x:int32)

method {:extern "QUICFFI", "ffi_mitls_global_free"} ffi_mitls_global_free(pv:voidptr)

method {:extern "QUICFFI", "newconnection_FFI"} newconnection_FFI(connection_state:voidptr, cs:connection) returns (x:voidptr)

method {:extern "QUICFFI", "createTimer_onLossDetectionAlarm"} createTimer_onLossDetectionAlarm(cs: connection) returns (x:voidptr)

method {:extern "QUICFFI", "createTimer_onPingAlarm"} createTimer_onPingAlarm(cs: connection) returns (x:voidptr)

}
