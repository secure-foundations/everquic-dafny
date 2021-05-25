#include "common.h"
#include "handwritten-dot-h-files/QUICUtils.h"

namespace QUICUtils {

DafnyArray<uint8> __default::build_buffer(DafnySequence<uint8> s,
                                          uint32 length) {
  DafnyArray<uint8> ret(s.ptr(), s.ptr() + s.len);
  return ret;
}

uint16 __default::load16_be(DafnyArray<uint8> b, uint32 offset) {
  uint16 result = 0;
  for (uint8 i = 0; i < 2; i++) {
    result = (result << 8) + b[offset + i];
  }
  return result;
}

uint32 __default::load32_be(DafnyArray<uint8> b, uint32 offset) {
  uint32 result = 0;
  for (uint8 i = 0; i < 4; i++) {
    result = (result << 8) + b[offset + i];
  }
  return result;
}

uint64 __default::load64_be(DafnyArray<uint8> b, uint32 offset) {
  uint64 result = 0;
  for (uint8 i = 0; i < 8; i++) {
    result = (result << 8) + b[offset + i];
  }
  return result;
}

void __default::store16_be(DafnyArray<uint8> b, uint32 offset, uint16 value) {
  for (uint8 i = 2; i > 0; i--) {
    b[offset + i - 1] = (value & 0xff);
    value = value >> 8;
  }
}

void __default::store32_be(DafnyArray<uint8> b, uint32 offset, uint32 value) {
  for (uint8 i = 4; i > 0; i--) {
    b[offset + i - 1] = (value & 0xff);
    value = value >> 8;
  }
}

void __default::store64_be(DafnyArray<uint8> b, uint32 offset, uint64 value) {
  for (uint8 i = 8; i > 0; i--) {
    b[offset + i - 1] = (value & 0xff);
    value = value >> 8;
  }
}

uint32 __default::load32_le(DafnyArray<uint8> b) {
  uint32 result = 0;
  for (uint8 i = 0; i < 4; i++) {
    result = (result << 8) + b[3 - i];
  }
  return result;
}

void __default::blit(DafnyArray<uint8> src, uint32 src_offset,
                     DafnyArray<uint8> dst, uint32 dst_offset, uint32 count) {
  for (uint32 i = 0; i < count; i++) {
    dst[dst_offset + i] = src[src_offset + i];
  }
}

uint32 __default::append_sequence(DafnyArray<uint8> dest, uint32 offset,
                                  DafnySequence<uint8> src, uint32 src_length) {
  for (uint32 i = 0; i < src_length; i++) {
    uint32_t number = (uint32_t)src.select(i);
    dest[offset + i] = src.select(i);
  }
  return offset + src_length;
}

void __default::dump_buffer(DafnyArray<uint8> src, uint32 offset, uint32 len) {
  cerr << "[DEBUG DFY BUF] " << dump(src, offset, len);
}

} // namespace QUICUtils
