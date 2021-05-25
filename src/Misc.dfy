
module Misc {

  function flatten_clear<T>(nested: set<set<T>>) : set<T>
  {
    set x, y | y in nested && x in y :: x
  }

  // Lemmas about sets

  lemma lemma_set_union_commute_once<T>(a:set<T>, b:set<T>)
    ensures a + b == b + a
  {}

  lemma lemma_set_union_commutes<T>()
    ensures forall a : set<T>, b : set<T> {:trigger a + b} :: a + b == b + a
  {}

  lemma lemma_set_union_associate_once<T>(a:set<T>, b:set<T>, c:set<T>)
    ensures (a + b) + c == a + (b + c)
  {}

  lemma lemma_set_union_associates<T>()
    ensures forall a : set<T>, b : set<T>, c : set<T> {:trigger ((a + b) + c), (a + (b + c))} :: (a + b) + c == a + (b + c)
  {}

  lemma lemma_set_facts<T>()
    ensures forall a : set<T>, b : set<T> {:trigger a + b} :: a + b == b + a
    ensures forall a : set<T>, b : set<T>, c : set<T> {:trigger ((a + b) + c), (a + (b + c))} :: (a + b) + c == a + (b + c)
  {}

}
