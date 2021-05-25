#pragma once

#include "DafnyRuntime.h" 
namespace QUICFFI {
using voidptr = DafnyArray<uint64>;

class __default {
  public:
    static int32 ffi_mitls_init();
    static int32 ffi_mitls_find_custom_extension (int32 is_server, DafnyArray<uint8> exts, voidptr ext_len, uint16 ext_type, DafnyArray<DafnyArray<uint8>> ext_data, voidptr ext_data_len) ;
    template <typename CFG>
    static int32 ffi_mitls_quic_create(DafnyArray<voidptr> cs,  DafnyArray<CFG> cfg); 

    template <typename QUIC_PROCESS_CTX>
    static int32 ffi_mitls_quic_process(voidptr quic_state, std::shared_ptr<QUIC_PROCESS_CTX> ctr, uint32 outbuf_offset);
    static void ffi_mitls_quic_free(voidptr state);
    static int32 ffi_mitls_quic_get_record_secrets(voidptr state, DafnyArray<uint8> client_secret, DafnyArray<uint8> server_secret, int32 epoch);
    static void ffi_mitls_global_free(voidptr pv);

    template <typename CONN>
    static voidptr newconnection_FFI(voidptr connection_state, CONN cs);

    template <typename CONN>
    static voidptr  createTimer_onLossDetectionAlarm(CONN cs);

    template <typename CONN>
    static voidptr  createTimer_onPingAlarm(CONN cs);
};
}
