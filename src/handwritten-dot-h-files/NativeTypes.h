#pragma once

#include "DafnyRuntime.h"

namespace NativeTypes {
class __default {
    public: 
      static uint8   xor8(uint8 x, uint8 y);
      static uint16  xor16(uint16 x, uint16 y);
      static uint32  xor32(uint32 x, uint32 y);
      static uint64  xor64(uint64 x, uint64 y);
      static uint8  or8(uint8 x, uint8 y);
      static uint16  or16(uint16 x, uint16 y);
      static uint32  or32(uint32 x, uint32 y);
      static uint64  or64(uint64 x, uint64 y);
      static uint8  and8(uint8 x, uint8 y);
      static uint16  and16(uint16 x, uint16 y);
      static uint32  and32(uint32 x, uint32 y);
      static uint64  and64(uint64 x, uint64 y);
      static uint8  lshift8(uint8 x, uint8 y);
      static uint16  lshift16(uint16 x, uint16 y);
      static uint32  lshift32(uint32 x, uint32 y);
      static uint64  lshift64(uint64 x, uint64 y);
      static uint64  not64(uint64 x);
};
}
