include "NativeTypes.dfy"

module {:extern "Extern"} Extern {
  import opened NativeTypes

method {:extern "Extern", "newArrayFill"} newArrayFill<T>(n: uint64, t: T) returns (ar: array<T>)
  ensures ar.Length == n as int
  ensures forall i | 0 <= i < n :: ar[i] == t
  ensures fresh(ar)


  method {:extern "Extern", "fatal"} fatal(m:string)
    ensures false

  method {:extern "Extern", "fatal_assume"} fatal_assume(ghost b:bool)
    ensures b;
}
