include "NativeTypes.dfy"

module ColdArray {
  import opened NativeTypes

class {:extern} FreezableArray<T> {
  function {:axiom} frozen() : bool
    reads this
 
  function {:axiom} contents() : seq<T>
    reads this

  constructor {:extern} (len:uint64)
    ensures !frozen()
    ensures |contents()| == len as int

  method {:extern} get(index:uint64) returns (ret:T)
    requires index as int < |contents()|
    ensures ret == contents()[index]

  method {:extern} put(index:uint64, val:T)
    requires index as int < |contents()|
    requires !frozen()
    modifies this
    ensures  !frozen()
    ensures  contents() == old(contents()[index as int := val])

  method {:extern} freeze()
    requires !frozen()
    modifies this
    ensures  frozen()
    ensures  contents() == old(contents())

  method {:extern} to_seq() returns (s:seq<T>)
    requires frozen()
    ensures  s == contents()

}


}
