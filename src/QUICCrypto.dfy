include "Options.dfy"
include "NativeTypes.dfy"
include "QUICDataTypes.dfy"
include "QUICConstants.dfy"
include "Extern.dfy"

// NOTE: This module forms part of the FFI interface. This is what
//             connects it up to everquic-crypto

module QUICCrypto {
    import opened Options
    import opened NativeTypes
    import opened QUICDataTypes
    import opened QUICConstants
    import opened Extern

    type u2 = uint2
    type u4 = i:uint8 | 0 <= i < 16
    type u32 = uint32
    type u32_upto20 = cil_t
    type u62 = uint62
    type u64 = uint64

    datatype long_header_specifics =
        | BInitial(
                payload_length: u62,
                packet_number_length: u62,
                token: buffer_t,
                token_length: u32
                )
        | BZeroRTT(
                payload_length: u62,
                packet_number_length: u62
                )
        | BHandshake(
                payload_length: u62,
                packet_number_length: u62
                )
        | BRetry(
                unused: u4,
                odcid: buffer_t,
                odcil: u32_upto20
                )

    datatype header =
        | BLong(
                version: u32,
                dcid: buffer_t,
                dcil: u32_upto20,
                scid: buffer_t,
                scil: u32_upto20,
                spec: long_header_specifics
                )
        /*
        [typ] long header types

        [version] QUIC version

        [dcil] Destination Connection ID length (bytes)

        [scil] Source Connection ID length (bytes)

        [dcid] Destination Connection ID

        [scid] Source Connection ID
        */
        | BShort(
                spin: bool,
                phase: bool,
                cid: buffer_t,
                cid_len: u32_upto20,
                packet_number_length: u64
        )
        /*
        [spin] Latency Spin Bit

        [phase] Key Phase

        [cid] Destination Connection ID

        [cid_len] Destination Connection ID length ?
        */

    method {:extern "QUICCrypto", "last_packet_number_of_state"} last_packet_number_of_state(s:state) returns (pn:u64)

    method {:extern "QUICCrypto", "create_in_st"} create_in_st(
      dst:Pointer<state>,
      initial_pn: u62,
      traffic_secret: buffer_t,
      r: Pointer<error_code>)
      requires dst != null
      requires dst[0] == null
      requires traffic_secret != null
      requires r != null
      modifies r
      modifies dst
      ensures r != null
      ensures r[0] == Success ==> (
              && dst[0] != null
              && fresh(dst[0])
          )
      ensures r[0] != Success ==> (
              && dst[0] == null
              && r[0] == UnsupportedAlgorithm
          )

    datatype error_code =
        | Success
        | UnsupportedAlgorithm
        | InvalidKey
        | AuthenticationFailure
        | InvalidIVLength
        | DecodeError

    type plain_len_t = l:uint32 | 0 == l || 3 <= l

    function method is_retry(h:header) : bool
    {
      h.BLong? && h.spec.BRetry?
    }

    function method has_payload_length(h:header) : bool
    {
      h.BLong? && (!h.spec.BRetry?)
    }

    function method {:extern "QUICCrypto", "header_len"} header_len(h:header) : u32

    method {:extern "QUICCrypto", "encrypt"} encrypt(
        s:state,
        dst: buffer_t,
        dst_pn: Pointer<u62>,
        h:header,
        plain:buffer_t,
        plain_len:plain_len_t,
        r: Pointer<error_code>)
        requires plain != null
        requires plain.Length >= plain_len as int
        requires dst_pn != null
        requires is_retry(h) ==> plain_len == 0;
        requires !is_retry(h) ==> 3 <= plain_len;
        requires has_payload_length(h) ==> h.spec.payload_length as int == plain_len as int + 16;
        requires dst != null;
        requires dst.Length >= header_len(h) as int + (if is_retry(h) then 0 else plain_len as int + 16);
        modifies s
        requires r != null
        modifies r
        modifies dst
        modifies dst_pn
        ensures dst_pn != null
        ensures r != null

    method {:extern "QUICCrypto", "initial_secrets"} initial_secrets(
      dst_client:buffer_t,
      dst_server:buffer_t,
      cid:buffer_t,
      cid_len:u32)
      requires dst_client != null;
      requires dst_server != null;
      requires cid != null;
      requires cid.Length == cid_len as int;
      requires cid_len <= 20;
      requires dst_client != dst_server && dst_server != cid && cid != dst_client;
      modifies dst_client;
      modifies dst_server;
      ensures dst_client != null;
      ensures dst_server != null;

    datatype result = result(
        pn: u62,
        header: header,
        header_len: u32,
        plain_len: u32,
        total_len: u32)

    method {:extern "QUICCrypto", "decrypt"} decrypt(
        s:state,
        dst: Pointer<result>,
        packet: buffer_t,
        packet_offset: u32,
        len:u32,
        cid_len: cil_t,
        r: Pointer<error_code>)
        requires packet != null
        requires dst != null
        requires 21 <= len
        requires packet_offset as int + len as int <= packet.Length
        requires r != null
        modifies r
        modifies packet
        modifies dst
        modifies s
        ensures r != null
        ensures (r[0] == Success) ==> (
            && (dst[0].header_len as int + dst[0].plain_len as int <= dst[0].total_len as int)
            && (dst[0].total_len <= len)
            && (dst[0].header.BLong? ==> (
                && dst[0].header.dcid != null
                && dst[0].header.scid != null
                && dst[0].header.dcid.Length == dst[0].header.dcil as int
                && dst[0].header.scid.Length == dst[0].header.scil as int))
            )
}
