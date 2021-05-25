include "Options.dfy"
include "NativeTypes.dfy"
include "Extern.dfy"

module OverFlowCheck {
import opened Options
import opened NativeTypes
import opened Extern

method FailOnOverflowAdd_u8(x:uint8, y:uint8)
  ensures x as int + y as int < 0x100
{
  if y >= 0xff - x {
    fatal("int-overflow");
  }
}

method FailOnOverflowAdd_u16(x:uint16, y:uint16)
  ensures x as int + y as int < 0x10000
{
  if y >= 0xffff - x {
    fatal("int-overflow");
  }
}

method FailOnOverflowAdd_u32(x:uint32, y:uint32)
  ensures x as int + y as int < 0x100000000
{
  if y >= 0xffffffff - x {
    fatal("int-overflow");
  }
}

method FailOnOverflowAdd_u62(x:uint62, y:uint62)
  ensures x as int + y as int <= UINT62_MAX as int
{
  if y >= UINT62_MAX - x {
    fatal("int-overflow");
  }
}


method FailOnOverflowMultiply_u8(x:uint8, y:uint8)
  ensures x as int * y as int < 0x100
{
  if x != 0 && y >= 0xff / x {
    fatal("int-overflow");
  }
}

method FailOnOverflowMultiply_u16(x:uint16, y:uint16)
  ensures x as int * y as int < 0x10000
{
  if x != 0 && y >= 0xffff / x {
    fatal("int-overflow");
  }
}

method FailOnOverflowMultiply_u32(x:uint32, y:uint32)
  ensures x as int * y as int < 0x100000000
{
  if x != 0 && y >= 0xffffffff / x {
    fatal("int-overflow");
  }
}

method safe_sub_uint62(x:uint62, y:uint62) returns (z: uint62)
    ensures z as int == x as int - y as int;
{
    if x < y {
        fatal("int-underflow");
    }
    z := x - y;
}


method safe_add_uint64(x:uint64, y:uint64) returns (z: uint64)
    ensures z as int == x as int + y as int;
{
    if y >= UINT64_MAX - x {
        fatal("int-overflow");
    }
    z := x + y;
}

method safe_mul_uint64(x:uint64, y:uint64) returns (z : uint64)
{
    if x != 0 && y >= UINT64_MAX / x {
        fatal("int-overflow");
    }
    assert 0 <= x as int * y as int < 0x10000000000000000; // OBSERVE
    z := x * y;
}

method safe_sub_uint64(x:uint64, y:uint64) returns (z: uint64)
    ensures z as int == x as int - y as int;
{
    if x < y {
        fatal("int-underflow");
    }
    z := x - y;
}

method safe_div_uint64(x:uint64, y:uint64) returns (z: uint64)
    ensures y != 0 && z as int == x as int / y as int;
{
    if y == 0 {
        fatal("div by zero");
    }
    z := x / y;
}

}
