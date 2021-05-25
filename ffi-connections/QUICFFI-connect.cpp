#include "common.h"
#include "handwritten-dot-h-files/QUICFFI.h"

extern "C" {
#include "mipki.h"
#include "mitlsffi.h"
#include "quic_provider.h"
}
#include <chrono>
#include <cstdlib>
#include <cstring>
#include <deque> // because vector<mutex> isn't possible to do, due to move/copy constructor issues
#include <iostream>
#include <memory>
#include <mutex>
#include <sstream>

namespace QUICFFI {

using intptr = DafnyArray<uint64>;
using namespace QUICFFI_Compile;
using namespace QUICDataTypes_Compile;
using namespace QConnection_Compile;
using loss = QUICLossAndCongestion_Compile::__default;

int32 ffi_mitls_init() {
  return FFI_mitls_init();
}

int32 __default::ffi_mitls_find_custom_extension(
    int32 is_server, DafnyArray<uint8> exts, DafnyArray<uint64> ext_len,
    uint16 ext_type, DafnyArray<DafnyArray<uint8>> ext_data,
    DafnyArray<uint64> ext_data_len) {
  cerr << "[DEBUGCALL].....ffi_mitls_find_custom_extension....." << endl;

  unsigned char **c_ext_data = NULL;
  size_t *c_ext_data_len = 0;
  int32 result =
      FFI_mitls_find_custom_extension(is_server, (exts).ptr(), (ext_len)[0],
                                      ext_type, c_ext_data, c_ext_data_len);

  (ext_data_len)[0] = *c_ext_data_len;
  (ext_data).clear_and_resize(*c_ext_data_len);
  for (size_t i = 0; i < *c_ext_data_len; i++) {
    DafnyArray<uint8> st(c_ext_data[i],
                         c_ext_data[i] + strlen((const char *)c_ext_data[i]));
    (ext_data)[i] = st;
  }

  return result;
}

typedef struct {
  mipki_state *pki;
  bool is_server;
} cb_state_t;

void *certificate_select(void *cbs, mitls_version ver, const unsigned char *sni,
                         size_t sni_len, const unsigned char *alpn,
                         size_t alpn_len, const mitls_signature_scheme *sigalgs,
                         size_t sigalgs_len, mitls_signature_scheme *selected) {
  cb_state_t *state = (cb_state_t *)cbs;
  mipki_chain r = mipki_select_certificate(
      state->pki, (const char *)sni, sni_len, sigalgs, sigalgs_len, selected);
  return (void *)r;
}

size_t certificate_format(void *cbs, const void *cert_ptr,
                          unsigned char *buffer) {
  cb_state_t *state = (cb_state_t *)cbs;
  mipki_chain chain = (mipki_chain)cert_ptr;
  return mipki_format_chain(state->pki, cert_ptr, (char *)buffer,
                            MAX_CHAIN_LEN);
}

size_t certificate_sign(void *cbs, const void *cert_ptr,
                        const mitls_signature_scheme sigalg,
                        const unsigned char *tbs, size_t tbs_len,
                        unsigned char *sig) {
  cb_state_t *state = (cb_state_t *)cbs;
  size_t ret = MAX_SIGNATURE_LEN;

  fprintf(stderr, "======== TO BE SIGNED <%04x>: (%zd octets) ========\n",
          sigalg, tbs_len);
  fprintf(stderr, "===================================================\n");

  if (mipki_sign_verify(state->pki, cert_ptr, sigalg, (const char *)tbs,
                        tbs_len, (char *)sig, &ret, MIPKI_SIGN))
    return ret;

  return 0;
}

int certificate_verify(void *cbs, const unsigned char *chain_bytes,
                       size_t chain_len, const mitls_signature_scheme sigalg,
                       const unsigned char *tbs, size_t tbs_len,
                       const unsigned char *sig, size_t sig_len) {
  cb_state_t *state = (cb_state_t *)cbs;
  mipki_chain chain =
      mipki_parse_chain(state->pki, (const char *)chain_bytes, chain_len);

  if (chain == NULL) {
    fprintf(stderr, "ERROR: failed to parse certificate chain");
    return 0;
  }

  // We don't validate hostname, but could with the callback state
  if (!mipki_validate_chain(state->pki, chain, "")) {
    fprintf(stderr, "WARN: chain validation failed, ignoring.\n");
  }

  size_t slen = sig_len;
  if (!mipki_sign_verify(state->pki, chain, sigalg, (const char *)tbs, tbs_len,
                         (char *)sig, &slen, MIPKI_VERIFY)) {
    fprintf(stderr, "ERROR: invalid signature.\n");
    return 0;
  }

  mipki_free_chain(state->pki, chain);
  return 1;
}

mipki_state *init_mipki() {
  // Server PKI configuration: one ECDSA certificate
  mipki_config_entry pki_config[1] = {{
      .cert_file = "../data/server-ecdsa.crt",
      .key_file = "../data/server-ecdsa.key",
      .is_universal = 1 // ignore SNI
  }};

  int erridx;

  mipki_state *pki = mipki_init(pki_config, 1, NULL, &erridx);

  if (!pki) {
    cerr << "[ERROR] Failed to initialize PKI library: errid=" << erridx
         << endl;
    return NULL;
  }

  if (!mipki_add_root_file_or_path(pki, "../data/CAFile.pem")) {
    cerr << "[ERROR] failed to add CAFile\n";
    return NULL;
  }
  return pki;
}

const char *pvname(mitls_version pv) {
  switch (pv) {
  case TLS_SSL3:
    return "SSL 3.0";
  case TLS_1p0:
    return "TLS 1.0";
  case TLS_1p1:
    return "TLS 1.1";
  case TLS_1p2:
    return "TLS 1.2";
  case TLS_1p3:
    return "TLS 1.3";
  }
  return "(unknown)";
}
mitls_nego_action def_action = TLS_nego_accept;

mitls_nego_action nego_cb(void *cb_state, mitls_version ver,
                          const unsigned char *cexts, size_t cexts_len,
                          mitls_extension **custom_exts,
                          size_t *custom_exts_len, unsigned char **cookie,
                          size_t *cookie_len) {
  printf(" @@@@ Nego callback for %s @@@@\n", pvname(ver));
  printf("Offered extensions:\n");
  cerr << dump(cexts, 0, cexts_len);

  unsigned char *qtp = NULL;
  size_t qtp_len;

  int r = FFI_mitls_find_custom_extension(((cb_state_t *)cb_state)->is_server, cexts, cexts_len, (uint16_t)0xffa5u,
                                          &qtp, &qtp_len);
  assert(r && qtp != NULL && qtp_len > 0);
  printf("Transport parameters offered:\n");
  cerr << dump(qtp, 0, qtp_len);

  if (*cookie != NULL && *cookie_len > 0) {
    printf("Stateless cookie found, application contents:\n");
    cerr << dump(*cookie, 0, *cookie_len);
  } else {
    printf("No application cookie (fist connection).\n");
  }

  // only used when TLS_nego_retry is returned, but it's safe to set anyway
  *cookie = (unsigned char *)"Hello World";
  *cookie_len = 11;

  *custom_exts = (mitls_extension *)malloc(sizeof(mitls_extension));
  *custom_exts_len = 1;
  custom_exts[0]->ext_type = (uint16_t)0xffa5u;
  custom_exts[0]->ext_data = (const unsigned char*) "\x00\x35\x00\x05\x00\x04\x80\x04\x00\x00\x00\x06\x00\x04\x80\x04\x00\x00\x00\x07\x00\x04\x80\x04\x00\x00\x00\x04\x00\x04\x80\x10\x00\x00\x00\x08\x00\x01\x01\x00\x09\x00\x02\x40\x64\x00\x01\x00\x01\x00\x00\x0e\x00\x01\x07";
  custom_exts[0]->ext_data_len = 55;
  printf("Adding server transport parameters:\n");
  cerr << dump(custom_exts[0]->ext_data, 0, custom_exts[0]->ext_data_len);

  printf(" @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n");
  fflush(stdout);
  return def_action;
}

// Workaround to make the compiler NOT complain about "explicit
// specialization after implicit initialization". Basically, since we
// are placing all of these `-connect` files _after_ all of their use
// cases are already specified, we are NOT allowed to specialize on
// the type, except we _need_ specialization on the type to be able to
// even talk about what we've got to get done. So, the workaround we
// use is to write a generic function that calls out to a specialized
// one here. This is why we introduce a new declaration, followed by a
// specialization immediately after, following which is the call to
// this specialized version.
template <typename CFG>
inline int32 _ffi_mitls_quic_create(DafnyArray<voidptr> cs,
                                    DafnyArray<CFG> cfg);
template <>
inline int32 _ffi_mitls_quic_create(DafnyArray<voidptr> cs,
                                    DafnyArray<quic__config> cfg) {

  mipki_state *pki = init_mipki();
  if (pki == NULL) {
    abort_with("[ERROR] mipki init failed");
  }

  cerr << "[INFO] mipki init complete";

  cb_state_t *cb_state = (cb_state_t *)malloc(sizeof(cb_state_t));
  cb_state->pki = pki;

  quic_state *qs = NULL;
  quic__config &qc = (cfg)[0];
  quic_config qcfg;

  mitls_cert_cb cert_callbacks = {.select = certificate_select,
                                  .format = certificate_format,
                                  .sign = certificate_sign,
                                  .verify = certificate_verify};
  cb_state->is_server = static_cast<bool>(qc.is__server);

	mitls_extension client_qtp[1] = {
			{// QUIC transport parameters (client)
				.ext_type = (uint16_t)0xffa5u,
				.ext_data =
					(const unsigned char*) "\x00\x35\x00\x05\x00\x04\x80\x04\x00\x00\x00\x06\x00\x04\x80\x04\x00\x00\x00\x07\x00\x04\x80\x04\x00\x00\x00\x04\x00\x04\x80\x10\x00\x00\x00\x08\x00\x01\x01\x00\x09\x00\x02\x40\x64\x00\x01\x00\x01\x00\x00\x0e\x00\x01\x07",
				.ext_data_len = 55}};

	mitls_alpn alpn = {.alpn = (const unsigned char *)"h3-24", .alpn_len = 5};

  quic_config config = {
      .is_server = static_cast<uint8_t>(qc.is__server),
      .enable_0rtt = 0,
      .host_name = "localhost",
      .alpn = &alpn,
      .alpn_count = 1,
      .server_ticket = NULL,
      .exts = client_qtp,
      .exts_count = 1,
      .callback_state = cb_state,
      .ticket_callback = NULL,
      .nego_callback = nego_cb,
      .cert_callbacks = &cert_callbacks,
      .cipher_suites = "TLS_CHACHA20_POLY1305_SHA256:TLS_AES_128_GCM_SHA256",
      .signature_algorithms = "ECDSA+SHA256:RSAPSS+SHA256",
      .named_groups = "X25519",
      .ticket_enc_alg = NULL,
      .ticket_key = NULL,
      .ticket_key_len = 0};

  int32 ret = FFI_mitls_quic_create(&qs, &config);

  (cs)[0] = voidstar_to_voidptr(qs);

  return ret;
}
template <typename CFG>
int32 __default::ffi_mitls_quic_create(DafnyArray<voidptr> cs,
                                       DafnyArray<CFG> cfg) {
  cerr << "[DEBUGCALL].....ffi_mitls_quic_create....." << endl;
  return _ffi_mitls_quic_create(cs, cfg);
}

// Specialization workaround
template <typename QUIC_PROCESS_CTX>
int32 _ffi_mitls_quic_process(voidptr quic_state,
                              shared_ptr<QUIC_PROCESS_CTX> ctr,
                              uint32 outbuf_offset);
template <>
int32 _ffi_mitls_quic_process(voidptr quic_state_,
                              shared_ptr<quic__process__ctx> ctr,
                              uint32 outbuf_offset) {
  quic_state *qs = (quic_state *)voidptr_to_voidstar(quic_state_);
  quic__process__ctx &dctx = (*ctr);

  quic_process_ctx ctx{};

  ctx.input = dctx.input.ptr();
  ctx.input_len = (dctx.input__len);
  ctx.output = dctx.output.ptr() + outbuf_offset; // NOTICE THIS.
  ctx.output_len = (dctx.output__len);
  // rest are outputs, we'll just copy _from_ them after the call

  std::ostringstream oss;

  oss << "[DEBUG] ctx dump before\n"
      << "reader key: " << dctx.cur__reader__key << "\n"
      << "writer key: " << dctx.cur__writer__key << "\n"
      << "input: " << dump(ctx.input, 0, ctx.input_len);

  int32 ret = FFI_mitls_quic_process(qs, &ctx); // ctx is inout, so
                                                // we need to copy
                                                // back too.

  // copy only output/inout stuff back
  dctx.output__len = (ctx.output_len);
  dctx.consumed__bytes = (ctx.consumed_bytes);
  dctx.to__be__written = (ctx.to_be_written);
  std::string tls_error_desc = ctx.tls_error_desc ? ctx.tls_error_desc : "";
  dctx.tls__error__desc = DafnySequenceFromString(tls_error_desc);
  dctx.cur__reader__key = ctx.cur_reader_key;
  dctx.cur__writer__key = ctx.cur_writer_key;
  dctx.flags = ctx.flags;

  oss << "[DEBUG] ctx dump after\n"
      << "reader key: " << dctx.cur__reader__key << "\n"
      << "writer key: " << dctx.cur__writer__key << "\n"
      << "output: " << dump(ctx.output, 0, ctx.output_len)
      << "completed: " << (ctx.flags & QFLAG_COMPLETE) << "\n";

  oss.flush();
  cerr << oss.str();

  return ret;
}
template <typename QUIC_PROCESS_CTX>
int32 __default::ffi_mitls_quic_process(voidptr quic_state,
                                        shared_ptr<QUIC_PROCESS_CTX> ctr,
                                        uint32 outbuf_offset) {
  cerr << "[DEBUGCALL].....ffi_mitls_quic_process....." << endl;
  return _ffi_mitls_quic_process(quic_state, ctr, outbuf_offset);
}

void __default::ffi_mitls_quic_free(voidptr state) {
  cerr << "[DEBUGCALL].....ffi_mitls_quic_free....." << endl;
  quic_state *qs = (quic_state *)voidptr_to_voidstar(state);
  FFI_mitls_quic_free(qs);
}

int32 __default::ffi_mitls_quic_get_record_secrets(voidptr state,
                                                   DafnyArray<uint8> client_secret,
                                                   DafnyArray<uint8> server_secret,
                                                   int32 epoch) {
  cerr << "[DEBUGCALL].....ffi_mitls_quic_get_record_secrets....." << endl;
  quic_state *qs = (quic_state *)voidptr_to_voidstar(state);
  quic_secret *crs = new quic_secret();
  quic_secret *srs = new quic_secret();

  assert(FFI_mitls_quic_get_record_secrets(qs, epoch, crs, srs) != 0);

  client_secret.assign(crs->secret, crs->secret + 64);
  server_secret.assign(srs->secret, srs->secret + 64);

  free(crs);
  free(srs);

  return 1;
}
void __default::ffi_mitls_global_free(voidptr pv) {
  cerr << "[DEBUGCALL].....ffi_mitls_global_free....." << endl;
  FFI_mitls_global_free(voidptr_to_voidstar(pv));
}

voidptr (*con_cb)(voidptr, shared_ptr<connection>);

// Specialization workaround
template <typename CONN>
voidptr _newconnection_FFI(voidptr connection_state, CONN cs);
template <>
voidptr _newconnection_FFI(voidptr connection_state,
                           shared_ptr<connection> cs) {
  return con_cb(connection_state, cs);
}
template <typename CONN>
voidptr __default::newconnection_FFI(voidptr connection_state, CONN cs) {
  cerr << "[DEBUGCALL].....newconnection_FFI....." << endl;
  return _newconnection_FFI(connection_state, cs);
}

voidptr create_connection_timer(
    shared_ptr<connection> cs, std::string name_of_f,
    std::function<void(voidptr, shared_ptr<connection>, voidptr)> f) {
  cerr << "[DEBUGCALL].....create_connection_timer....." << endl;
  connection_timers_mtx.lock();
  uint64 ret = connection_timers.size();
  connection_timers.emplace_back();

  auto &timer = connection_timers[ret];

  timer.conn = cs;
  timer.cancelled = false;
  timer.scheduled_time = 0;

  std::thread([&timer, f, name_of_f]() {
    voidptr ignore = voidstar_to_voidptr(NULL);
    while (true) {
      std::unique_lock<std::mutex> lck(timer.mtx);
      timer.cv.wait(lck);
      if (!timer.cancelled) {
        f(ignore, timer.conn, ignore);
      }
    }
  })
      .detach();

  connection_timers_mtx.unlock();
  return voidstar_to_voidptr((void *)ret);
}

// Specialization workaround
template <typename CONN> voidptr _createTimer_onLossDetectionAlarm(CONN cs);

template <>
voidptr _createTimer_onLossDetectionAlarm(shared_ptr<connection> cs) {
  return create_connection_timer(cs, "lossDetectionAlarm",
                                 loss::onLossDetectionAlarm);
}

template <typename CONN>
voidptr __default::createTimer_onLossDetectionAlarm(CONN cs) {
  return _createTimer_onLossDetectionAlarm(cs);
}

// Specialization workaround
template <typename CONN> voidptr _createTimer_onPingAlarm(CONN cs);
template <> voidptr _createTimer_onPingAlarm(shared_ptr<connection> cs) {
  return create_connection_timer(cs, "pingAlarm", loss::onPingAlarm);
}

template <typename CONN> voidptr __default::createTimer_onPingAlarm(CONN cs) {
  return _createTimer_onPingAlarm(cs);
}

} // namespace QUICFFI
