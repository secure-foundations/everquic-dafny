#pragma once

#include "DafnyRuntime.h"

using namespace std;

namespace QUICCrypto {

  class __default {
    public:
      template<typename STATE>
      static uint64 last_packet_number_of_state(STATE s);

      template<typename STATE, typename ERRCODE>
      static void create_in_st(DafnyArray<STATE> dst, uint64 initial_pn, DafnyArray<uint8> trafic_secret, DafnyArray<ERRCODE> err);

      template<typename HEADER>
      static uint32 header_len(HEADER h);

      template<typename STATE, typename HEADER, typename ERRCODE>
      static void encrypt(DafnyArray<STATE> s,
                   DafnyArray<uint8> dst,
                   DafnyArray<uint64> dst_pn,
                   HEADER h,
                   DafnyArray<uint8> plain,
                   uint32 plain_len,
                   DafnyArray<ERRCODE> err);

      static void initial_secrets(DafnyArray<uint8> dst_client,
                           DafnyArray<uint8> dst_server,
                           DafnyArray<uint8> cid,
                           uint32 cid_len);

      template<typename STATE, typename RESULT, typename ERRCODE>
      static void decrypt(DafnyArray<STATE> s,
                   DafnyArray<RESULT> dst,
                   DafnyArray<uint8> packet,
                   uint32 packet_offset,
                   uint32 len,
                   uint8 cid_len,
                   DafnyArray<ERRCODE> err);
  };

}
