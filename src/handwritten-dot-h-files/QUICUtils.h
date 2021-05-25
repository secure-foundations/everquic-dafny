#pragma once

#include "DafnyRuntime.h"

namespace QUICUtils {

  class __default {
    public:
      static DafnyArray<uint8> build_buffer(DafnySequence<uint8> s, uint32 length); 
      static uint16 load16_be (DafnyArray<uint8> b, uint32 offset);
      static uint32 load32_be (DafnyArray<uint8> b, uint32 offset); 
      static uint64 load64_be (DafnyArray<uint8> b, uint32 offset); 
      static void store16_be (DafnyArray<uint8> b, uint32 offset, uint16 value);
      static void store32_be (DafnyArray<uint8> b, uint32 offset, uint32 value);
      static void store64_be (DafnyArray<uint8> b, uint32 offset, uint64 value);
      static uint32 load32_le(DafnyArray<uint8> b);
      static void blit(DafnyArray<uint8> src, uint32 src_offset, DafnyArray<uint8> dst, uint32 dst_offset, uint32 count);

      static uint32 append_sequence(DafnyArray<uint8> dest, uint32 offset, DafnySequence<uint8> src, uint32 src_length);
      static void dump_buffer(DafnyArray<uint8> src, uint32 offset, uint32 len);
  };

}
