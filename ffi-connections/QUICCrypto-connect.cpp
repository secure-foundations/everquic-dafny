#include "common.h"
#include "handwritten-dot-h-files/QUICCrypto.h"

extern "C" {
#include "EverQuic.h"
}
#include <cstdlib>
#include <sstream>

using namespace std;

namespace QUICDataTypes_Compile {
struct state_s {
  EverQuic_state_s *p;
};
} // namespace QUICDataTypes_Compile

namespace QUICCrypto {

using namespace QUICDataTypes_Compile;
using namespace QUICCrypto_Compile;

typedef DafnyArray<state_s> state;
typedef error__code error_code;

static EverQuic_index quiccrypto_index = {
    .hash_alg = Spec_Hash_Definitions_SHA2_256,
    .aead_alg = Spec_Agile_AEAD_AES128_GCM,
};

// Specialization workaround
template <typename STATE> uint64 _last_packet_number_of_state(STATE s);
template <> uint64 _last_packet_number_of_state(state s) {
  cerr << "[DEBUGCALL].....last_packet_number_of_state....." << endl;
  return EverQuic_last_packet_number_of_state(s[0].p);
}
template <typename STATE> uint64 last_packet_number_of_state(STATE s) {
  return _last_packet_number_of_state(s);
}

static inline error_code to_error_code(EverCrypt_Error_error_code e) {
  switch (e) {
  case EverCrypt_Error_Success:
    return error_code::create_Success();
  case EverCrypt_Error_UnsupportedAlgorithm:
    return error_code::create_UnsupportedAlgorithm();
  case EverCrypt_Error_InvalidKey:
    return error_code::create_InvalidKey();
  case EverCrypt_Error_AuthenticationFailure:
    return error_code::create_AuthenticationFailure();
  case EverCrypt_Error_InvalidIVLength:
    return error_code::create_InvalidIVLength();
  case EverCrypt_Error_DecodeError:
    return error_code::create_DecodeError();
  default:
    cerr << "[ERROR] Reached impossible condition in to_error_code" << endl;
    abort();
  }
}

// Specialization workaround
template <typename STATE, typename ERRCODE>
void _create_in_st(DafnyArray<STATE> dst, uint64 initial_pn,
                   DafnyArray<uint8> traffic_secret, DafnyArray<ERRCODE> err);
template <>
void _create_in_st(DafnyArray<state> dst, uint64 initial_pn,
                   DafnyArray<uint8> traffic_secret,
                   DafnyArray<error_code> err) {
#ifdef DEBUG
  cerr << "[DEBUGCALL].....create_in_st....." << endl;
  cerr << "[DEBUG] pn = " << initial_pn
       << ", secret = " << dump(traffic_secret);
#endif
  state dest(1);
  error_code result = to_error_code(EverQuic_create_in(
      quiccrypto_index, &(dest)[0].p, initial_pn, (traffic_secret).ptr()));
  (err)[0] = result;
  if (result.is_error__code_Success()) {
    dst[0] = dest;
  }
}
template <typename STATE, typename ERRCODE>
void __default::create_in_st(DafnyArray<STATE> dst, uint64 initial_pn,
                             DafnyArray<uint8> traffic_secret,
                             DafnyArray<ERRCODE> err) {
  _create_in_st(dst, initial_pn, traffic_secret, err);
}

static inline EverQuic_header to_quicimpl_header(header h) {
  EverQuic_header res;
  if (h.is_header_BLong()) {
    res.tag = EverQuic_BLong;
    res.case_BLong.version = h.dtor_version();
    res.case_BLong.dcid = (h.dtor_dcid()).ptr();
    res.case_BLong.dcil = h.dtor_dcil();
    res.case_BLong.scid = (h.dtor_scid()).ptr();
    res.case_BLong.scil = h.dtor_scil();
    EverQuic_long_header_specifics &spec = res.case_BLong.spec;
    long__header__specifics lh = h.dtor_spec();
    if (lh.is_long__header__specifics_BInitial()) {
      spec.tag = EverQuic_BInitial;
      spec.case_BInitial.reserved_bits = 0; // XXX[reserved_bits_change]
      spec.case_BInitial.payload_and_pn_length =
          lh.dtor_payload__length() + lh.dtor_packet__number__length(); // XXX[payload_length_change]
      spec.case_BInitial.packet_number_length =
          lh.dtor_packet__number__length();
      spec.case_BInitial.token = (lh.dtor_token()).ptr();
      spec.case_BInitial.token_length = lh.dtor_token__length();
    } else if (lh.is_long__header__specifics_BZeroRTT()) {
      spec.tag = EverQuic_BZeroRTT;
      spec.case_BZeroRTT.reserved_bits = 0; // XXX[reserved_bits_change]
      spec.case_BZeroRTT.payload_and_pn_length =
          lh.dtor_payload__length() + lh.dtor_packet__number__length(); // XXX[payload_length_change]
      spec.case_BZeroRTT.packet_number_length =
          lh.dtor_packet__number__length();
    } else if (lh.is_long__header__specifics_BHandshake()) {
      spec.tag = EverQuic_BHandshake;
      spec.case_BHandshake.reserved_bits = 0; // XXX[reserved_bits_change]
      spec.case_BHandshake.payload_and_pn_length =
          lh.dtor_payload__length() + lh.dtor_packet__number__length(); // XXX[payload_length_change]
      spec.case_BHandshake.packet_number_length =
          lh.dtor_packet__number__length();
    } else if (lh.is_long__header__specifics_BRetry()) {
      spec.tag = EverQuic_BRetry;
      spec.case_BRetry.unused = lh.dtor_unused();
      spec.case_BRetry.odcid = (lh.dtor_odcid()).ptr();
      spec.case_BRetry.odcil = lh.dtor_odcil();
    }
  } else if (h.is_header_BShort()) {
    res.tag = EverQuic_BShort;
    res.case_BShort.spin = h.dtor_spin();
    res.case_BShort.phase = h.dtor_phase();
    res.case_BShort.cid = (h.dtor_cid()).ptr();
    res.case_BShort.cid_len = h.dtor_cid__len();
    res.case_BShort.packet_number_length = h.dtor_packet__number__length();
  }
  return res;
}

// Specialization workaround
template <typename HEADER> uint32 _header_len(HEADER h);
template <> uint32 _header_len(header h) {
  return EverQuic_header_len(to_quicimpl_header(h));
}
template <typename HEADER> uint32 __default::header_len(HEADER h) {
  return _header_len(h);
}

// Specialization workaround
template <typename STATE, typename HEADER, typename ERRCODE>
void _encrypt(DafnyArray<STATE> s, DafnyArray<uint8> dst,
              DafnyArray<uint64> dst_pn, HEADER h, DafnyArray<uint8> plain,
              uint32 plain_len, DafnyArray<ERRCODE> err);
template <>
void _encrypt(state s, DafnyArray<uint8> dst, DafnyArray<uint64> dst_pn,
              header h, DafnyArray<uint8> plain, uint32 plain_len,
              DafnyArray<error_code> err) {
  uint64_t dstpn;
#ifdef DEBUG
  cerr << "[DEBUG] plain = " << dump(plain, 0, plain_len);
#endif

  err[0] = to_error_code(EverQuic_encrypt(s[0].p, (dst).ptr(), &dstpn,
                                           to_quicimpl_header(h), (plain).ptr(),
                                           plain_len));
  dst_pn[0] = dstpn;

  uint32_t cipher_len = plain_len + _header_len(h) + 16;

#ifdef DEBUG
  cerr << "[DEBUG] dst = " << dump(dst, 0, cipher_len);
#endif
}
template <typename STATE, typename HEADER, typename ERRCODE>
void __default::encrypt(DafnyArray<STATE> s, DafnyArray<uint8> dst,
                        DafnyArray<uint64> dst_pn, HEADER h,
                        DafnyArray<uint8> plain, uint32 plain_len,
                        DafnyArray<ERRCODE> err) {
  _encrypt(s, dst, dst_pn, h, plain, plain_len, err);
}

void __default::initial_secrets(DafnyArray<uint8> dst_client,
                                DafnyArray<uint8> dst_server,
                                DafnyArray<uint8> cid, uint32 cid_len) {

  EverQuic_initial_secrets((dst_client).ptr(), (dst_server).ptr(), (cid).ptr(),
                            cid_len);
  cerr << "[DEBUGCALL].....initial_secrets....." << endl;
}

static inline long__header__specifics
to_long_header_specifics(EverQuic_long_header_specifics &l) {
  switch (l.tag) {
  case EverQuic_BInitial: {
    DafnyArray<uint8> ret(l.case_BInitial.token,
                          l.case_BInitial.token + l.case_BInitial.token_length);
    if (l.case_BInitial.reserved_bits != 0) {
      // XXX[reserved_bits_change]
      cerr << "[ERROR] Reached bad reserved_bits for BInitial in "
           << "to_long_header_specifics ; got "
           << ((uint64)l.case_BInitial.reserved_bits) << endl;
      abort();
    }
    return long__header__specifics::create_BInitial(
        l.case_BInitial.payload_and_pn_length - l.case_BInitial.packet_number_length, // XXX[payload_length_change]
        l.case_BInitial.packet_number_length,
        ret, l.case_BInitial.token_length);
  }
  case EverQuic_BZeroRTT: {
    if (l.case_BZeroRTT.reserved_bits != 0) {
      // XXX[reserved_bits_change]
      cerr << "[ERROR] Reached bad reserved_bits for BZeroRTT in "
           << "to_long_header_specifics ; got "
           << ((uint64)l.case_BZeroRTT.reserved_bits) << endl;
      abort();
    }
    return long__header__specifics::create_BZeroRTT(
        l.case_BZeroRTT.payload_and_pn_length - l.case_BZeroRTT.packet_number_length, // XXX[payload_length_change]
        l.case_BZeroRTT.packet_number_length);
  }
  case EverQuic_BHandshake: {
    if (l.case_BHandshake.reserved_bits != 0) {
      // XXX[reserved_bits_change]
      cerr << "[ERROR] Reached bad reserved_bits for BHandshake in "
           << "to_long_header_specifics ; got "
           << ((uint64)l.case_BHandshake.reserved_bits) << endl;
      abort();
    }
    return long__header__specifics::create_BHandshake(
        l.case_BHandshake.payload_and_pn_length - l.case_BHandshake.packet_number_length, // XXX[payload_length_change]
        l.case_BHandshake.packet_number_length);
  }
  case EverQuic_BRetry: {
    DafnyArray<uint8> ret(l.case_BRetry.odcid,
                          l.case_BRetry.odcid + l.case_BRetry.odcil);
    return long__header__specifics::create_BRetry(l.case_BRetry.unused, ret,
                                                  l.case_BRetry.odcil);
  }
  default:
    cerr << "[ERROR] Reached impossible condition in to_long_header_specifics"
         << endl;
    abort();
  }
}

static inline header to_header(EverQuic_header &h) {
  switch (h.tag) {
  case EverQuic_BLong: {
    DafnyArray<uint8> ret_d(h.case_BLong.dcid,
                            h.case_BLong.dcid + h.case_BLong.dcil);
    DafnyArray<uint8> ret_s(h.case_BLong.scid,
                            h.case_BLong.scid + h.case_BLong.scil);
    return header::create_BLong(h.case_BLong.version, ret_d, h.case_BLong.dcil,
                                ret_s, h.case_BLong.scil,
                                to_long_header_specifics(h.case_BLong.spec));
  }
  case EverQuic_BShort: {
    DafnyArray<uint8> ret(h.case_BShort.cid,
                          h.case_BShort.cid + h.case_BShort.cid_len);
    return header::create_BShort(h.case_BShort.spin, h.case_BShort.phase, ret,
                                 h.case_BShort.cid_len,
                                 h.case_BShort.packet_number_length);
  }
  default:
    cerr << "[ERROR] Reached impossible condition in to_header ; got "
         << ((uint64)h.tag) << endl;
    abort();
  }
}

static inline result to_result(EverQuic_result &r) {
  return result(r.pn, to_header(r.header), r.header_len, r.plain_len,
                r.total_len);
}

// Specialization workaround
template <typename STATE, typename RESULT, typename ERRCODE>
void _decrypt(DafnyArray<STATE> s, DafnyArray<RESULT> dst,
              DafnyArray<uint8> packet, uint32 packet_offset, uint32 len,
              uint8 cid_len, DafnyArray<ERRCODE> err);
template <>
void _decrypt(state s, DafnyArray<result> dst, DafnyArray<uint8> packet,
              uint32 packet_offset, uint32 len, uint8 cid_len,
              DafnyArray<error_code> err) {
#ifdef DEBUG
  cerr << "[DEBUG] decrypting packet = " << dump(packet, packet_offset, len);
#endif

  EverQuic_result qidst;
  uint32_t r = EverQuic_decrypt((s)[0].p, &qidst, (packet).ptr() + packet_offset, len, cid_len);

  (err)[0] = to_error_code(r);
  if ((err)[0].is_error__code_Success()) {
    (dst)[0] = to_result(qidst);
#ifdef DEBUG
    cerr << "[DEBUG] decrypted = "
         << dump(packet, qidst.header_len, qidst.plain_len);
#endif
  } else {
#ifdef DEBUG
    cerr << "[DEBUG] Got error code " <<  r << endl;
#endif
  }
}
template <typename STATE, typename RESULT, typename ERRCODE>
void __default::decrypt(DafnyArray<STATE> s, DafnyArray<RESULT> dst,
                        DafnyArray<uint8> packet, uint32 packet_offset,
                        uint32 len, uint8 cid_len, DafnyArray<ERRCODE> err) {
  _decrypt(s, dst, packet, packet_offset, len, cid_len, err);
}

} // namespace QUICCrypto

// Undefine things that KreMLin defines, that causes clashes with what
// we've defined.
#undef load16_be
#undef load32_be
#undef load64_be
#undef store16_be
#undef store32_be
#undef store64_be
#undef load16_le
#undef load32_le
#undef load64_le
