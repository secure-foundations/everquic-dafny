#include "handwritten-dot-h-files/NativeTypes.h"

namespace NativeTypes {
#define OP(O, N, T)                                                            \
  uint##T __default::N##T(uint##T x, uint##T y) { return x O y; }
#define OPS(O, N) OP(O, N, 8) OP(O, N, 16) OP(O, N, 32) OP(O, N, 64)
OPS(^, xor)
OPS(|, or)
OPS(&, and)
OPS(<<, lshift)
#undef OP
#undef OPS
uint64 __default::not64(uint64 x) { return ~x; }
} // namespace NativeTypes
