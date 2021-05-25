module Seqs {
  function last<T>(s:seq<T>) : T
    requires |s| > 0;
  {
    s[|s|-1]
  }

  function all_but_last<T>(s:seq<T>) : seq<T>
    requires |s| > 0;
  {
    s[..|s|-1]
  }

  function reverse<T>(s:seq<T>) : seq<T>
    ensures |reverse(s)| == |s|
  {
    if s == [] then []
    else reverse(s[1..]) + [s[0]]
  }
}
