include "Options.dfy"
include "NativeTypes.dfy"
include "QUICDataTypes.dfy"
include "PrivateDLL.dfy"
include "Extern.dfy"
include "FreezableArray.dfy"

module QUICUtils {
    import opened Options
    import opened NativeTypes
    import opened QUICDataTypes
    import opened PrivateDLL
    import opened Extern
    import opened ColdArray

// Append a uint64 value to the buffer. Returns the next write offset.
method append64 (b:buffer<byte>, offset:uint32, value:uint64) returns (x:uint32)
    requires b != null;
    requires offset as int <= b.Length - 8
    ensures  x == offset + 8;
{
    store64_be (b, offset, value);
    return offset + 8;
}

// Append a uint32 value to the buffer.  Returns the next write offset.
method append32 (b:buffer<byte>, offset:uint32, value:uint32) returns (x:uint32)
    requires b != null;
    requires offset as int <= b.Length - 4
    ensures  x == offset + 4;
{
    store32_be(b, offset, value);
    return offset + 4;
}

// Append a uint16 value to the buffer.  Returns the next write offset.
method append16 (b:buffer<byte>, offset:uint32, value:uint16) returns (x:uint32)
    requires b != null;
    requires offset as int <= b.Length - 2
    ensures  x == offset + 2;
{
    store16_be(b, offset, value);
    return offset + 2;
}

// Append a uint8 value to the buffer.  Returns the next write offset.
method append8 (b:buffer<byte>, offset:uint32, value:byte) returns (x:uint32)
    requires b != null;
    requires offset as int <= b.Length - 1
    modifies b;
    ensures  x == offset + 1;
{
    b[offset] := value;
    return offset + 1;
}

// Append raw bytes to a buffer.  Returns the next write offset.
method append_buffer (dest:buffer<byte>, offset:uint32, src:buffer<byte>, src_length:uint32) returns (x:uint32)
    requires dest != null && src != null;
    requires offset as int + src_length as int <= dest.Length;
    requires src_length as int <= src.Length;
    modifies dest;
    ensures  x == offset + src_length;
{
    blit(src, 0, dest, offset, src_length);
    return offset + src_length;
}

method {:extern "QUICUtils", "append_sequence"} append_sequence (dest:buffer<byte>, offset:uint32, src:seq<byte>, src_length:uint32) returns (x:uint32)
    requires dest != null;
    requires offset as int + src_length as int <= dest.Length;
    requires src_length as int <= |src|;
    modifies dest;
    ensures  x == offset + src_length;


/* getbytes "safe" - read out of buffer 'b' with length 'l' at offset 'offset' into value/valuelength.
    Returns the next write offset. */
method getbytes_s (b:buffer<byte>, l:uint32, offset:uint32, value:buffer<byte>, valuelength:uint32) returns (x:Err<uint32>)
    requires b != null && value != null;
    requires l as int <= b.Length;
    requires valuelength as int <= value.Length;
    modifies value;
    ensures x.Ok? ==> x.value as int == valuelength as int + offset as int;
{
    if offset as uint64 + valuelength as uint64 >= l as uint64 {
        return Fail("Insufficient buffer");
    }
    blit(b, offset, value, 0, valuelength);
    return Ok(offset + valuelength);
}

// Read a uint64 from the buffer
method getu64 (b:buffer<byte>, offset:uint32) returns (x:uint64)
    requires b != null;
    requires offset as int <= b.Length - 8
    ensures true
{
    x := load64_be(b, offset);
}

// Read a uint32 from the buffer
method getu32 (b:buffer<byte>, offset:uint32) returns (x:uint32)
    requires b != null;
    requires offset as int <= b.Length - 4
    ensures true
{
    x := load32_be(b, offset);
}

/* Read "safely" a uint32 from the buffer.  Returns the value or an
    error if the read is past the end of the buffer. */
method getu32_s (b:buffer<byte>, l:uint32, offset:uint32) returns (x:Err<uint32>)
    requires b != null;
    requires l as int <= b.Length;
    ensures true
{
    if offset as uint64 + 4 >= l as uint64 {
        return Fail("Insufficient buffer");
    }
    var u := load32_be(b, offset);
    return Ok(u);
}

// Read a uint16 from the buffer
method getu16 (b:buffer<byte>, offset:uint32) returns (x:uint16)
    requires b != null;
    requires offset as int <= b.Length - 2
    ensures true
{
    x := load16_be(b, offset);
}


  /* Read "safely" a uint16 from the buffer.  Returns the value or an
         error if the read is past the end of the buffer. */
method getu16_s (b:buffer<byte>, l:uint32, offset:uint32) returns (x:Err<uint16>)
    requires b != null;
    requires l as int <= b.Length;
{
    if offset as uint64 + 2 >= l as uint64 {
        return Fail("Insufficient buffer");
    }
    var u := load16_be(b, offset);
    return Ok(u);
}

// Read a uint8 from the buffer
method getu8 (b:buffer<byte>, offset:uint32) returns (x:byte)
    requires b != null;
    requires offset as int <= b.Length - 1
    ensures  x == b[offset];
{
    return b[offset];
}

/* Read "safely" a uint8 from the buffer.  Returns the value or an
        error if the read is past the end of the buffer. */
method getu8_s (b:buffer<byte>, l:uint32, offset:uint32) returns (x:Err<byte>)
    requires b != null;
    requires l as int <= b.Length;
{
    if offset as uint64 >= l as uint64 {
      print("[WARN DFY] getu8_s - Insufficient buffer size: offset = ",
        offset, ", l = ", l, "\n");
      return Fail("Insufficient buffer");
    }
    return Ok(b[offset]);
}

  // Write a variable-length uint64.  The top 2 bits of the first byte will indicate the length of the full value.
method appendvar (b:buffer<byte>, offset:uint32, value:uint64) returns (x:Err<uint32>)
    requires b != null;
    requires offset as int < b.Length - 8
    modifies b;
    ensures x.Ok? ==> x.value <= offset + 8;
{
    if value < 0x40 {
        var o := append8(b, offset, value as byte);
        x := Ok(o);
    } else if value < 0x4000 {
        var v16 := value as uint16;
        v16 := or16(v16, 0x4000);
        var o := append16(b, offset, v16);
        x := Ok(o);
    } else if value < 0x40000000 {
        var v32 := value as uint32;
        v32 := or32(v32, 0x80000000);
        var o := append32(b, offset, v32);
        x := Ok(o);
    } else if value < 0x4000000000000000 {
        var v64 := value as uint64;
        v64 := or64(v64, 0xc000000000000000);
        var o := append64(b, offset, v64);
        x := Ok(o);
    } else {
        x := Fail("Value must be < 2^62");
    }
}

function method encoded_size (value:uint64) : Err<uint32>
{
    if value < 0x40 then Ok(1)
    else if value < 0x4000 then Ok(2)
    else if value < 0x40000000 then Ok(4)
    else if value < 0x4000000000000000 then Ok(8)
    else Fail("Value must be < 2^62")
}

function method decode_variable_size(len:uint8) : uint8
{
    if len == 0 then 1
    else if len == 0x40 then 2
    else if len == 0x80 then 4
    else 8
}

function var_length(b:seq<byte>) : nat
    requires |b| >= 1
{
    var first := b[0];
    var len := xor8(first, 0xc0);
    decode_variable_size(len) as nat
}

// this version does not throw any exception
method encode_variable_strict(b:buffer<byte>, offset:uint32, value:uint62)
    returns (o:uint32)
    requires b != null;
    requires offset as int + encoded_size_strict(value) as int <= b.Length
    modifies b;
    ensures o == offset + encoded_size_strict(value);
    ensures o as int <= b.Length;
{
    if value < 0x40 {
        o := append8(b, offset, value as uint8);
    } else if value < 0x4000 {
        var v16 := or16(value as uint16, 0x4000);
        o := append16(b, offset, v16);
    } else if value < 0x40000000 {
        var v32 := or32(value as uint32, 0x80000000);
        o := append32(b, offset, v32);
    } else if value < 0x4000000000000000 {
        var v64 := or64(value as uint64, 0xc000000000000000);
        o := append64(b, offset, v64);
    }
}

// this version throws exception, with minimal precondition
method encode_variable_loose(b:buffer<byte>, buffer_len:uint32, offset:uint32, value:uint64)
    returns (o:Err<uint32>)
    requires b != null;
    requires buffer_len as int <= b.Length;
    modifies b;
{
    if value > UINT62_MAX { return Fail("invalid value"); }
    if offset >= buffer_len { return Fail("invalid offset"); }
    var remaining_length := buffer_len - offset;
    if remaining_length < 8 { return Fail("insufficient buffer space"); }
    var o' := encode_variable_strict(b, offset, value as uint62);
    return Ok(o');
}

method encode_vairable_fxied_legth(buffer: buffer<byte>, initial_offset: uint32, value: uint62)
    returns (offset: uint32)
    requires buffer != null && buffer.Length - initial_offset as int >= 8;
    modifies buffer;
    ensures offset == initial_offset + 8;
{
    offset := initial_offset;
    var v64 := or64(value as uint64, 0xc000000000000000);
    offset := append64(buffer, offset, v64);
}

method decode_variable_(buffer:buffer<byte>, length:uint32, offset: uint32, variable_size:uint8)
    returns (x: (uint62, uint32))
    requires offset as int + variable_size as int <= length as int;
    requires variable_size in {1, 2, 4,8};
    requires && buffer != null && length as int <= buffer.Length;
    ensures x.1 == offset + variable_size as uint32;
{
    if variable_size == 1 {
        var t8 := getu8(buffer, offset);
        return (t8 as uint62, offset + 1);
    }

    if variable_size == 2 {
        var t16 := getu16(buffer, offset);
        t16 := and16(t16, 0x3fff);
        return (t16 as uint62, offset + 2);
    }

    if variable_size == 4 {
        var t32 := getu32(buffer, offset);
        t32 := and32(t32, 0x3fffffff);
        return (t32 as uint62, offset + 4);
    }

    var t64 := getu64(buffer, offset);
    t64 := and64(t64, UINT62_MAX);
    return (t64 as uint62, offset + 8);
}

// this version throws exception, with minimal precondition
method decode_variable_loose(b:buffer<byte>, length:uint32, offset:uint32)
    returns (x:Err<(uint62, uint32)>)
    requires b != null;
    requires length as int <= b.Length;
    ensures x.Ok? ==> x.value.1 > offset && x.value.1 <= length;
{
    if offset as uint64 + 1 > length as uint64 { // cast so overflow won't happen
        return Fail("Insufficient buffer");
    }
    var first_byte := getu8(b, offset);
    var len_byte := and8(first_byte, 0xc0);

    var variable_size := decode_variable_size(len_byte);

    if offset as uint64 + variable_size as uint64 > length as uint64 { // cast so overflow won't happen
        return Fail("Insufficient buffer");
    }
    var v, offset';
    var ret := decode_variable_(b, length, offset, variable_size);
    v := ret.0;
    offset' := ret.1;
    return Ok((v, offset'));
}

method decode_length_loose(b:buffer<byte>, length:uint32, initial_offset:uint32) returns (x:Err<(uint32, uint32)>)
    requires b != null && length as int <= b.Length;
    ensures x.Ok? ==> initial_offset < x.value.1 <= length;
{
    var temp2 := decode_variable_loose(b, length, initial_offset);
    if temp2.Fail? { return Fail("deocde length failed"); }
    var length, parse_offset := temp2.value.0, temp2.value.1;
    if length > UINT32_MAX as uint62 { return Fail("decoded length makes no sense"); }
    return Ok((length as uint32, parse_offset));
}

// this version of encodedsize should be better
function method encoded_size_strict(value:uint62) : uint32
{
    if value < 0x40 then 1
    else if value < 0x4000 then 2
    else if value < 0x40000000 then 4
    else 8
}

predicate buffer_offset_valid_pre(packet:buffer_t, packet_len:uint32, p:uint32)
{
    && packet != null
    && packet_len as int <= packet.Length
    && p < packet_len
}

predicate buffer_offset_valid_pos(packet_len:uint32, initial_offset:uint32, x:Err<uint32>)
{
    x.Ok? ==> initial_offset < x.value <= packet_len
}

predicate buffer_offset_valid_pos2(packet_len:uint32, initial_offset:uint32, x:Err<process_result>)
{
    x.Ok? ==> initial_offset < x.value.offset <= packet_len
}

predicate buffer_valid(packet:buffer_t, packet_len:uint32)
{
    packet != null&&  packet_len as int <= packet.Length && packet_len != 0
}

method build_buffer_from_seq(s:seq<byte>, l:uint32) returns (a:buffer<byte>)
    requires |s| == l as int;
    ensures a != null && |s| == a.Length;
    ensures fresh(a);
{
  a := new byte[l];
  var i : uint32 := 0;
  while i < l
    invariant 0 <= i <= l;
    invariant a != null;
    invariant |s| == l as int;
    invariant |s| == a.Length;
    decreases l - i;
  {
    a[i] := s[i];
    i := i + 1;
  }
}

method {:extern "QUICUtils", "load16_be"} load16_be (b:buffer<byte>, offset:uint32) returns (v:uint16)
    requires b != null;
    requires offset as int <= b.Length - 2

method {:extern "QUICUtils", "load32_be"} load32_be (b:buffer<byte>, offset:uint32) returns (v:uint32)
    requires b != null;
    requires offset as int <= b.Length - 4

method {:extern "QUICUtils", "load64_be"} load64_be (b:buffer<byte>, offset:uint32) returns (v:uint64)
    requires b != null;
    requires offset as int <= b.Length - 8

method {:extern "QUICUtils", "store16_be"} store16_be (b:buffer<byte>, offset:uint32, value:uint16)
    requires b != null;
    requires offset as int <= b.Length - 2

method {:extern "QUICUtils", "store32_be"} store32_be (b:buffer<byte>, offset:uint32, value:uint32)
    requires b != null;
    requires offset as int <= b.Length - 4

method {:extern "QUICUtils", "store64_be"} store64_be (b:buffer<byte>, offset:uint32, value:uint64)
    requires b != null;
    requires offset as int <= b.Length - 8

method {:extern "QUICUtils", "load32_le"} load32_le(b:buffer<byte>) returns (v:uint32)
    requires b != null;
    requires b.Length >= 4

method {:extern "QUICUtils", "blit"} blit(src:buffer<byte>, src_offset:uint32, dst:buffer<byte>, dst_offset:uint32, count:uint32)
    requires src != null && dst != null;
    requires src_offset as int + count as int <= src.Length;
    requires dst_offset as int + count as int <= dst.Length;

method {:extern "QUICUtils", "dump_buffer"} dump_buffer(src:buffer<byte>, offset:uint32, len:uint32)

method print_connection_id(id: connection_id_fixed)
{
    var buffer := build_buffer_from_seq(id.cid, id.len as uint32);
    print("[DEBUG DFY] cid ");
    dump_buffer(buffer, 0, id.len as uint32);
}

method build_sub_buffer(src:buffer<byte>, src_len:uint32, src_offset:uint32, dst_len:uint32)
    returns (dst: buffer<byte>)
    requires src != null && src_len as int <= src.Length 
    requires src_offset as int + dst_len as int <= src_len as int;
    ensures fresh(dst);
    ensures (dst != null && dst.Length == dst_len as int);
{
    dst := new byte[dst_len];
    var i := 0;

    while i < dst_len
    {
        dst[i] := src[i + src_offset];
        i := i + 1;
    }
}

method list_to_seq<T>(list:PrivateDoublyLinkedList<T>, empty:T)
    returns (x:(seq<T>, uint32))
    requires list.Valid();
    ensures |x.0| == x.1 as int;
{
    var is_empty := list.IsEmpty();
    if is_empty { return ([], 0); }

    // fist count the number of elements
    var count : uint32 := 0;
    var keepgoing := true;
    var iter := new DllIterator(list);

    while keepgoing
        invariant list.Valid()
        invariant keepgoing ==> iter.Valid()
        invariant keepgoing ==> iter.d == list
        invariant !keepgoing ==> iter.GetIndex() == |list.Vals|

        invariant count as int == iter.GetIndex();
        decreases |list.Vals| - iter.GetIndex(), keepgoing
    {
        var _ := iter.GetVal(); // we have to put GetVal here, otherwise can't prove the decrease clause
        if count == UINT32_MAX {
            fatal("lr list too long");
        }
        count := count + 1;
        keepgoing := iter.MoveNext();
    }

    assert count as int == |list.Vals|;

    var f_arr := new FreezableArray<T>(count as uint64);
    assert count as int == |f_arr.contents()|;

    iter := new DllIterator(list);
    var i := 0;
    keepgoing := true;

    while keepgoing
        invariant count as int == |list.Vals|;
        invariant i as nat == iter.GetIndex();
        invariant i <= count;
        invariant list.Valid()
        invariant keepgoing ==> iter.Valid()
        invariant keepgoing ==> iter.d == list
        invariant !f_arr.frozen();
        invariant count as int == |f_arr.contents()|;
        decreases |list.Vals| - iter.GetIndex(), keepgoing
    {
        if i == count { break; }
        var val := iter.GetVal();
        f_arr.put(i as uint64, val);
        i := i + 1;
        keepgoing := iter.MoveNext();
    }

    f_arr.freeze();
    var s := f_arr.to_seq();
    x := (s, count);
}

}
