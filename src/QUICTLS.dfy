include "Options.dfy"
include "NativeTypes.dfy"
// include "BitVectors.dfy"
include "QEngine.dfy"
include "QUICUtils.dfy"
include "QUICFFI.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "QConnection.dfy"
include "Extern.dfy"

/*
QUIC TLS - the CRYPTO stream implementation

@summary:  CRYPTO frame producer and consumer
*/

module QUICTLS {

import opened Options
import opened NativeTypes
import opened QEngine
import opened QUICUtils
import opened QUICFFI
import opened QUICDataTypes
import opened QUICConstants
import opened QConnection
import opened Extern

const quic_transport_parameter_extension_type:uint16 := 0xffa5

// This is called by miTLS when the 0-RTT ticket is available
method onTicketReady (cs:connection, sni:string, ticket:Pointer<mitls_ticket>)
    requires cs.Valid();
    modifies cs;
    ensures cs.Valid();
{
    cs.tls_ticket := ticket;
}


method parse_transport_parameter(cs: connection, packet:buffer<byte>, packet_len:uint32, inital_offset:uint32)
    returns (x: (Err<uint16>, uint32))
    requires cs.Valid();
    requires buffer_offset_valid_pre(packet, packet_len, inital_offset);
    modifies cs.stream_manager`peer_max_data;
    modifies cs.stream_manager`peer_max_stream_data_bidi_local;
    ensures cs.Valid();
    ensures x.0.Ok? ==> inital_offset < x.1 <= packet_len;  // can be equal
    ensures packet == old(packet);
{
    var remaining_length := packet_len - inital_offset;
    var offset := inital_offset;

    if remaining_length < 4 {
        return (Fail("insufficient buffer space"), offset);
    }
    var parameter_id, paramter_length;

    parameter_id := getu16(packet, offset);
    offset := offset + 2;
    paramter_length := getu16(packet, offset);
    offset := offset + 2;

    remaining_length := packet_len - offset;

    if remaining_length <= paramter_length as uint32 {
        return (Fail("insufficient buffer space"), offset);
    }

    if parameter_id == STATELESS_RESET_TOKEN {
        if paramter_length != 16 { return (Fail("invalid STATELESS_RESET_TOKEN length"), offset); }
        // MUST NOT be sent by a client, but MAY be sent by a server.
        return (Ok(parameter_id), offset + 16);
    }
    if (parameter_id == PREFERRED_ADDRESS) {
        fatal("PREFERRED_ADDRESS unhandled");
    }
    if (parameter_id == DISABLE_ACTIVE_MIGRATION) {
        fatal("DISABLE_ACTIVE_MIGRATION unhandled");
    }

    var temp := decode_variable_loose(packet, packet_len, offset);
    var value;

    if temp.Fail? { return (Fail("failed to decode IDLE_TIMEOUT"), offset); }
    value, offset := temp.value.0, temp.value.1;

    if (parameter_id == ORIGINAL_CONNECTION_ID) {
        fatal("ORIGINAL_CONNECTION_ID unhandled");
    } else if (parameter_id == IDLE_TIMEOUT) {
        fatal("IDLE_TIMEOUT unhandled");
    } else if (parameter_id == MAX_PACKET_SIZE) {
        fatal("MAX_PACKET_SIZE unhandled");
    } else if (parameter_id == INITIAL_MAX_DATA) {
        cs.stream_manager.peer_max_data := value;
    } else if (parameter_id == INITIAL_MAX_STREAM_DATA_BIDI_LOCAL) {
        cs.stream_manager.peer_max_stream_data_bidi_local := value;
    } else if (parameter_id == INITIAL_MAX_STREAM_DATA_BIDI_REMOTE) {
        fatal("INITIAL_MAX_STREAM_DATA_BIDI_REMOTE unhandled");
    } else if (parameter_id == INITIAL_MAX_STREAM_DATA_UNI) {
        fatal("INITIAL_MAX_STREAM_DATA_UNI unhandled");
    } else if (parameter_id == INITIAL_MAX_STREAMS_BIDI) {
        fatal("INITIAL_MAX_STREAMS_BIDI unhandled");
    } else if (parameter_id == INITIAL_MAX_STREAMS_UNI) {
        fatal("INITIAL_MAX_STREAMS_UNI unhandled");
    } else if (parameter_id == ACK_DELAY_EXPONENT) {
        fatal("ACK_DELAY_EXPONENT unhandled");
    } else if (parameter_id == MAX_ACK_DELAY) {
        fatal("MAX_ACK_DELAY unhandled");
    } else if (parameter_id == ACTIVE_CONNECTION_ID_LIMIT) {
        fatal("ACTIVE_CONNECTION_ID_LIMIT unhandled");
    } else {
    	fatal("unkown parameter id");
    }
    return (Ok(parameter_id), offset);
}

// Parse a TransportParameters extension and update the local connection state with its value
method updatePeerParameters (cs:connection, packet:buffer_t, packet_len:uint32) returns (x:bool)
    requires packet != null && packet_len as int == packet.Length;
    requires cs.Valid();
    modifies cs.stream_manager`peer_max_data;
    modifies cs.stream_manager`peer_max_stream_data_bidi_local;
    ensures cs.Valid();
{
    if packet_len == 0 { return; }

    var offset := 0;

    while offset < packet_len
        invariant packet_len > 0;
        invariant buffer_offset_valid_pre(packet, packet_len, offset);
        invariant cs.Valid();
    {
        var parameter_id, temp;
        var pair := parse_transport_parameter(cs, packet, packet_len, offset);
        temp := pair.0;
        offset := pair.1;
        if temp.Fail? { return false; }
        parameter_id := temp.value;
        if offset == packet_len { break; } // need this to maintian invariant
    }

    return true;
}

// we will waste space and always use 12 bytes
method encode_quic_transport_variable_parameter(
        packet: buffer<byte>,
        inital_offset :uint32,
        parameter_id :uint16,
        value: uint62)
    returns (offset: uint32)
    requires packet != null;
    requires packet.Length - inital_offset as int >= 12;
    modifies packet;
    ensures offset == inital_offset + 12;
{
    offset := inital_offset;
    offset := append16(packet, offset, parameter_id);
    offset := append16(packet, offset, 8);
    offset := encode_vairable_fxied_legth(packet, offset, value);
}

// Encode a quic_transport_parameters field, of a buffer of bytes
method encode_quic_transport_array_parameter(
        packet: buffer<byte>,
        inital_offset: uint32,
        parameter_id: uint16,
        parameter: seq<uint8>,
        parameter_length:uint16)
    returns (offset: uint32)
    requires packet != null;
    requires packet.Length - inital_offset as int >= 4 + |parameter|;
    requires |parameter| == parameter_length as int;
    modifies packet;
    ensures inital_offset as int + 4 + |parameter| == offset as int;
{
    offset := inital_offset;
    offset := append16(packet, offset, parameter_id);
    offset := append16(packet, offset, parameter_length);
    offset := append_sequence(packet, offset, parameter, parameter_length as uint32);
}

// Create a transport_parameters block
method createTransportParameters (cs:connection) returns (x:Err<Pointer<mitls_extension>>)
{
    // Write in the TransportParameters
    var tp := new byte[256];
    var p := 2;

    p := encode_quic_transport_variable_parameter(tp, p, INITIAL_MAX_DATA, cs.stream_manager.local_max_data);
    p := encode_quic_transport_variable_parameter(tp, p, INITIAL_MAX_STREAMS_UNI, cs.stream_manager.local_max_streams_bidi);
    p := encode_quic_transport_variable_parameter(tp, p, INITIAL_MAX_STREAMS_BIDI, cs.stream_manager.local_max_streams_uni);
    p := encode_quic_transport_variable_parameter(tp, p, INITIAL_MAX_STREAM_DATA_BIDI_LOCAL, DEFAULT_MAX_STREAM_DATA);
    p := encode_quic_transport_variable_parameter(tp, p, INITIAL_MAX_STREAM_DATA_BIDI_REMOTE, DEFAULT_MAX_STREAM_DATA);
    p := encode_quic_transport_variable_parameter(tp, p, INITIAL_MAX_STREAM_DATA_UNI, DEFAULT_MAX_STREAM_DATA);

    if ! cs.cf_state.is_client {
      p := encode_quic_transport_array_parameter(tp, p, STATELESS_RESET_TOKEN, cs.cf_state.statelessResetToken, 16);
    }

    var _ := append16(tp, 2, (p - 2) as uint16); // write in the length of the Transport Parameters

    var result := new mitls_extension[1];
    var ext_data_len := newArrayFill(1, p as uint64);
    result[0] := mitls_extension(quic_transport_parameter_extension_type, tp, ext_data_len);
    return Ok(result);
}

// Callback from miTLS during the handshake
method onNegoInternal (cs:connection, vers:mitls_version, exts:buffer_t, exts_len:Pointer<uint64>) returns (x:(Err<mitls_nego_action>))
    requires cs.Valid();
    modifies cs.stream_manager`peer_max_data;
    modifies cs.stream_manager`peer_max_stream_data_bidi_local;
    ensures cs.Valid();
{
    if vers != TLS_1p3 {
        return Fail("Invalid TLS version");
    }

    var ptp;
    var ptp_len := newArrayFill(1,0);
    // 1 is server
    var r := ffi_mitls_find_custom_extension(1, exts, exts_len, quic_transport_parameter_extension_type, ptp, ptp_len);

    if r == 0 {
        return Fail("Failed to find the TransportParameters extension");
    }
    var result := updatePeerParameters(cs, ptp[0], ptp_len[0] as uint32);
    if result {
        return Ok(TLS_nego_accept);
    }
    return Fail("failed in updatePeerParameters");
}

// Callback from miTLS during negotiation.
method onNego (cs:connection, vers:mitls_version, exts:buffer_t, exts_len:Pointer<uint64>, custom_exts:Pointer<Pointer<mitls_extension>>, custom_exts_len: Pointer<uint64>, cookie:Pointer<buffer_t>, cookie_len:Pointer<uint64>) returns (x:mitls_nego_action)
    requires custom_exts != null && custom_exts_len != null;
    requires cs.Valid();
    modifies cs.stream_manager`peer_max_data;
    modifies cs.stream_manager`peer_max_stream_data_bidi_local;
    modifies custom_exts, custom_exts_len;
    ensures cs.Valid();
{
  var result := onNegoInternal(cs, vers, exts, exts_len);
  match result
    case Ok(r) =>
      if cs.cf_state.is_client {
        var tp_ext := createTransportParameters(cs);
        if tp_ext.Fail? {
          print "[DEBUG DFY] failed to create transport parameters\n";
          return TLS_nego_abort;
        }
        custom_exts[0] := tp_ext.value;
        custom_exts_len[0] := 1;
      }
      return r;
    case Fail(msg) =>
      print "[DEBUG DFY] Nego failed", msg, "\n";
      return TLS_nego_abort;
}

//   Initialize miTLS for a connection.  This is separate from initializing the
//   connection, to allow clients and servers an opportunity to specify configuration
//  options to miTLS.
method initialize_mitls_state(cs:connection) returns (x: quic_state)
{
    var is_client := cs.cf_state.is_client;
    var exts_ := createTransportParameters(cs);
    if exts_.Fail? { fatal(exts_.err); }
    var exts := exts_.value;

    var exts_count := newArrayFill(1, if is_client then 1 else 0);
    var signature_algorithms :=
        if is_client then "ECDSA+SHA256:ECDSA+SHA384:ECDSA+SHA512:RSAPSS+SHA256:RSAPSS+SHA384:RSAPSS+SHA512"
        else "RSAPSS+SHA512:RSAPSS+SHA384:RSAPSS+SHA256";

    var named_groups := if is_client then "X25519" else "X25519";
    var is_server := if is_client then 0 else 1;
    var hostname := cs.cf_state.hostname;
    var tkt := cs.tls_ticket;
    var len := newArrayFill(1, 5);
    var alpns_ptr := new mitls_alpn[1];
    alpns_ptr[0] := mitls_alpn("h3-24", len);

    var alpn_count := newArrayFill(1, 1);
    var cs_ptr := newArrayFill(1, cs);

    var cfg : quic_config := quic_config(
        is_server,
        alpns_ptr,
        alpn_count,
        "TLS_CHACHA20_POLY1305_SHA256:TLS_AES_128_GCM_SHA256",
        signature_algorithms,
        named_groups,
        0, // disable 0rtt
        hostname,
        tkt,
        exts,
        exts_count,
        cs_ptr,
        null,
        null,
        null);

    var cfg_ptr := newArrayFill(1, cfg);
    var state := new quic_state[1];


    var r := ffi_mitls_quic_create(state, cfg_ptr);

    if r != 1 {
        fatal("FFI_mitls_quic_create failed\n");
    }
    return state[0];
}

method get_tls_secrets(cs: connection, mitls_epoch:int32, is_client: bool) returns (crs: quic_key, srs: quic_key)
    ensures crs != null && srs != null;
{
    crs := new byte[64];
    srs := new byte[64];

    if is_client {
        var r := ffi_mitls_quic_get_record_secrets(cs.mitls_state, crs, srs, mitls_epoch);
    } else {
        var r := ffi_mitls_quic_get_record_secrets(cs.mitls_state, srs, crs, mitls_epoch);
    }
}

}
