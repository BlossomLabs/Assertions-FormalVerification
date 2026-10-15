include "../../../proof-tools/dafnyevm/src/dafny/core/memory.dfy"
module C50Stores {
  import opened Int
  import ByteUtils
  import U16
  import U32
  import U64
  import U128
  import U256
  import Arrays
  import Memory

  lemma Store8(mem:seq<u8>,a:nat,v:u8)
    requires a+1<=|mem|
    ensures ByteUtils.WriteUint8(mem,a,v)==mem[..a]+[v]+mem[a+1..]
  { assert mem[a:=v] == mem[..a]+[v]+mem[a+1..]; }

  lemma Store16(mem:seq<u8>,a:nat,v:u16)
    requires a+2<=|mem|
    ensures ByteUtils.WriteUint16(mem,a,v)==mem[..a]+U16.ToBytes(v)+mem[a+2..]
  {
    var high:=(v/(TWO_8 as u16)) as u8;
    var low:=(v%(TWO_8 as u16)) as u8;
    Store8(mem,a,high);
    var first:=ByteUtils.WriteUint8(mem,a,high);
    Store8(first,a+1,low);
  }

  lemma Store32(mem:seq<u8>,a:nat,v:u32)
    requires a+4<=|mem|
    ensures ByteUtils.WriteUint32(mem,a,v)==mem[..a]+U32.ToBytes(v)+mem[a+4..]
  {
    var high:=(v/(TWO_16 as u32)) as u16;
    var low:=(v%(TWO_16 as u32)) as u16;
    Store16(mem,a,high);
    var first:=ByteUtils.WriteUint16(mem,a,high);
    Store16(first,a+2,low);
  }

  lemma Store64(mem:seq<u8>,a:nat,v:u64)
    requires a+8<=|mem|
    ensures ByteUtils.WriteUint64(mem,a,v)==mem[..a]+U64.ToBytes(v)+mem[a+8..]
  {
    var high:=(v/(TWO_32 as u64)) as u32;
    var low:=(v%(TWO_32 as u64)) as u32;
    Store32(mem,a,high);
    var first:=ByteUtils.WriteUint32(mem,a,high);
    Store32(first,a+4,low);
  }

  lemma Store128(mem:seq<u8>,a:nat,v:u128)
    requires a+16<=|mem|
    ensures ByteUtils.WriteUint128(mem,a,v)==mem[..a]+U128.ToBytes(v)+mem[a+16..]
  {
    var high:=(v/(TWO_64 as u128)) as u64;
    var low:=(v%(TWO_64 as u128)) as u64;
    Store64(mem,a,high);
    var first:=ByteUtils.WriteUint64(mem,a,high);
    Store64(first,a+8,low);
  }

  lemma Store256(mem:seq<u8>,a:nat,v:u256)
    requires a+32<=|mem|
    ensures ByteUtils.WriteUint256(mem,a,v)==mem[..a]+U256.ToBytes(v)+mem[a+32..]
  {
    var high:=(v/(TWO_128 as u256)) as u128;
    var low:=(v%(TWO_128 as u256)) as u128;
    Store128(mem,a,high);
    var first:=ByteUtils.WriteUint128(mem,a,high);
    Store128(first,a+16,low);
  }
}
