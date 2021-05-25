include "Seqs.dfy"

module PrivateDLL {
  import opened Seqs

  export
    provides PrivateNode
    provides PrivateDoublyLinkedList
    provides PrivateDoublyLinkedList.Vals, PrivateDoublyLinkedList.Repr
    provides PrivateDoublyLinkedList.Valid
    provides PrivateDoublyLinkedList._ctor, PrivateDoublyLinkedList.IsEmpty
    provides PrivateDoublyLinkedList.RemoveHead, PrivateDoublyLinkedList.RemoveTail
    provides PrivateDoublyLinkedList.InsertHead, PrivateDoublyLinkedList.InsertTail
    provides PrivateDoublyLinkedList.PeekHead, PrivateDoublyLinkedList.PeekTail
    provides PrivateDoublyLinkedList.Clear

    provides Seqs
    provides DllIterator
    provides DllIterator.d
    provides DllIterator._ctor, DllIterator.Valid, DllIterator.GetIndex
    provides DllIterator.GetVal, DllIterator.MoveNext
    provides InsertBeforeIter, RemoveIter

  class PrivateNode<T> {
    var L: PrivateNode?<T>
    var R: PrivateNode?<T>
    var payload:T
    constructor (p:T)
      ensures payload == p;
    {
      payload := p;
    }
  }

  lemma find_index<T>(Nodes: seq<PrivateNode<T>>, Repr: set<PrivateNode<T>>, x:PrivateNode<T>) returns (k:nat)
      requires forall i :: 0 <= i < |Nodes| ==> Nodes[i] in Repr
      requires |Nodes| == |Repr|
      requires x in Repr;
      requires forall i,j :: 0 <= i < j < |Nodes| ==> Nodes[i] != Nodes[j]
      ensures 0 <= k < |Nodes| && Nodes[k] == x
    {
      if Nodes[0] == x {
        k := 0;
      } else {
        var rest_seq := Nodes[1..];
        var rest_set := Repr - {Nodes[0]};
        var k' := find_index(Nodes[1..], Repr - {Nodes[0]}, x);
        k := 1 + k';
      }
    }

  lemma exists_index<T>(Nodes: seq<PrivateNode<T>>, Repr: set<PrivateNode<T>>, x:PrivateNode<T>)
      requires forall i :: 0 <= i < |Nodes| ==> Nodes[i] in Repr
      requires |Nodes| == |Repr|
      requires x in Repr;
      requires forall i,j :: 0 <= i < j < |Nodes| ==> Nodes[i] != Nodes[j]
      ensures  exists k :: 0 <= k < |Nodes| && Nodes[k] == x
    {
      ghost var k := find_index(Nodes, Repr, x);
    }

  class PrivateDoublyLinkedList<T> {
    ghost var Nodes: seq<PrivateNode<T>>  // sequence of nodes in the linked list
    ghost var Repr: set<PrivateNode<T>>   // (redundant) representation of the list's footprint
    ghost var Vals: seq<T>
    var head:PrivateNode?<T>
    var tail:PrivateNode?<T>

    // Valid() says that the data structure is a proper doubly linked list
    predicate Valid()
      reads this, Repr
    {
      (forall i :: 0 <= i < |Nodes| ==> Nodes[i] in Repr) &&
      |Nodes| == |Repr| &&
      (|Nodes| == 0 <==> head == tail == null) &&
      (|Nodes| > 0 ==>
        head == Nodes[0] && tail == last(Nodes) &&
        Nodes[0].L == null &&  last(Nodes).R == null &&
        (forall i {:trigger Nodes[i].L} :: 1 <= i < |Nodes| ==> Nodes[i].L == Nodes[i-1]) &&
        (forall i {:trigger Nodes[i].R} :: 0 <= i < |Nodes|-1 ==> Nodes[i].R == Nodes[i+1])
      ) &&
      (forall i,j :: 0 <= i < j < |Nodes| ==> Nodes[i] != Nodes[j]) &&  // this is actually a consequence of the previous conditions
      |Nodes| == |Vals| &&
      (forall i :: 0 <= i < |Nodes| ==> Nodes[i].payload == Vals[i])
    }

    constructor()
      ensures Valid()
      ensures Vals == []
      ensures fresh(Repr)
    {
      Nodes := [];
      Repr := {};
      Vals := [];
      head := null;
      tail := null;
    }

    method IsEmpty() returns (b:bool)
      requires Valid();
      ensures b <==> (|Vals| == 0);
    {
      b := (head == null && tail == null);
    }

    // Internal method -- tends to be a bit flaky
    method Remove(x: PrivateNode<T>) returns (ghost k: int)
      requires Valid()
      requires x in Repr
      modifies this, Repr
      ensures Valid()
      ensures 0 <= k < |old(Nodes)| && x == old(Nodes)[k]
      ensures Nodes == old(Nodes)[..k] + old(Nodes)[k+1..]
      ensures Vals == old(Vals)[..k] + old(Vals)[k+1..]
      ensures x.L == old(x.L) && x.R == old(x.R) && x.payload == old(x.payload)
      ensures Repr == old(Repr) - {x}
      //ensures forall n :: n in old(Repr) ==> n.payload == old(n.payload)
    {
      //k :| 0 <= k < |Nodes| && Nodes[k] == x;
      k := find_index(Nodes, Repr, x);
      if (x.L == null && x.R == null) {
        Nodes := [];
        Repr := Repr - {x};
        head := null;
        tail := null;
        Vals := [];
      } else if (x.L == null) {
        assert k == 0;
        x.R.L := null;
        head := x.R;
        Nodes := Nodes[1..];
        Repr := Repr - {x};
        Vals := Vals[1..];
      } else if (x.R == null) {
        assert k == |Nodes| - 1;
        x.L.R := null;
        tail := x.L;
        Nodes := Nodes[..|Nodes|-1];
        assert old(Nodes)[k+1..] == [];
        Repr := Repr - {x};
        Vals := Vals[..|Vals|-1];
        assert old(Vals)[k+1..] == [];
      } else {
        x.R.L := x.L;
        x.L.R := x.R;
        Nodes := Nodes[..k] + Nodes[k+1..];
        Repr := Repr - {x};
        Vals := Vals[0..k] + Vals[k+1..];
        assert Vals == old(Vals)[..k] + old(Vals)[k+1..];
      }
    }

    method RemoveHead() returns (h:T)
      requires Valid()
      requires |Vals| != 0
      modifies this, Repr
      ensures Valid()
      ensures h == old(Vals)[0];
      ensures Vals == old(Vals)[1..]
      ensures forall o :: o in Repr ==> o in old(Repr);
    {
      h := head.payload;
      ghost var k := Remove(head);
    }

    method RemoveTail() returns (t:T)
      requires Valid()
      requires |Vals| != 0
      modifies this, Repr
      ensures Valid()
      ensures t == last(old(Vals));
      ensures Vals == all_but_last(old(Vals))
      ensures forall o :: o in Repr ==> o in old(Repr);
    {
      t := tail.payload;
      ghost var k := Remove(tail);
    }

    method InsertHead(v:T)
      requires Valid()
      modifies this, Repr
      ensures Valid()
      ensures Vals == [v] + old(Vals)
      ensures forall o :: o in Repr ==> o in old(Repr) || fresh(o)
    {
      var x := new PrivateNode(v);
      if head == null {
        head := x;
        tail := x;
        x.L := null;
        x.R := null;
        Nodes := [x];
        Repr := {x};
      } else {
        x.R := head;
        x.L := null;
        head.L := x;
        head := x;
        Nodes := [x] + old(Nodes);
        Repr := {x} + old(Repr);
      }
      Vals := [v] + Vals;
    }

    method InsertTail(v:T)
      requires Valid()
      modifies this, Repr
      ensures Valid()
      ensures Vals == old(Vals) + [v]
      ensures forall o :: o in Repr ==> o in old(Repr) || fresh(o)
    {
      var x := new PrivateNode(v);
      if tail == null {
        head := x;
        tail := x;
        x.L := null;
        x.R := null;
        Nodes := [x];
        Repr := {x};
      } else {
        x.L := tail;
        x.R := null;
        tail.R := x;
        tail := x;
        Nodes := old(Nodes) + [x];
        Repr := old(Repr) + {x};
      }
      Vals := Vals + [v];
    }

    method PeekHead() returns (v:T)
      requires Valid()
      requires |Vals| != 0
      ensures v == Vals[0]
    {
      v := head.payload;
    }

    method PeekTail() returns (v:T)
      requires Valid()
      requires |Vals| != 0
      ensures v == last(Vals)
    {
      v := tail.payload;
    }

    method Clear()
    requires Valid();
    modifies this, Repr;
    ensures  Valid();
    {
      Repr := {};
      Nodes := [];
      Vals := [];
      head := null;
      tail := null;
    }
  }

  class DllIterator<T> {
    var ptr:PrivateNode?<T>
    ghost var index:nat
    var d:PrivateDoublyLinkedList<T>

    predicate Valid()
      reads this, d, d.Repr
    {
       && d.Valid()
       && 0 <= index < |d.Nodes|
       && ptr == d.Nodes[index]
    }

    function GetIndex() : nat
      reads this
    {
      index
    }

    constructor (d':PrivateDoublyLinkedList<T>)
      requires d'.Valid()
      requires |d'.Vals| > 0
      ensures  Valid()
      ensures  d == d'
      ensures  GetIndex() == 0
    {
      d := d';
      ptr := d'.head;
      index := 0;
    }

    method GetVal() returns (v:T)
      requires Valid();
      ensures  0 <= GetIndex() < |d.Vals| && d.Vals[GetIndex()] == v;
    {
      return ptr.payload;
    }

    method MoveNext() returns (good:bool)
      requires Valid()
      modifies this;
      ensures good ==> Valid();
      ensures GetIndex() == old(GetIndex()) + 1;
      ensures !good ==> GetIndex() == |d.Vals|
      ensures d == old(d);
    {
      ptr := ptr.R;
      index := index + 1;
      if ptr != null {
        good := true;
      } else {
        good := false;
      }
    }
  }

  method InsertBeforeIter<T>(d:PrivateDoublyLinkedList<T>, iter:DllIterator<T>, v:T)
    requires iter.Valid() && iter.d == d
    modifies d, d.Repr
    ensures  d.Valid()
    //ensures  iter.Valid()
    ensures  d.Vals == old(d.Vals) [..iter.GetIndex()] + [v] + old(d.Vals) [iter.GetIndex()..]
    ensures  d.Vals[iter.GetIndex()] == v // Implied by the condition above
    ensures  forall o :: o in d.Repr ==> o in old(d.Repr) || fresh(o)
  {
    if iter.ptr == d.head {
      d.InsertHead(v);
      // Update iterator?
    } else {
      var x := new PrivateNode(v);
      x.L := iter.ptr.L;
      x.R := iter.ptr;
      iter.ptr.L.R := x;
      iter.ptr.L := x;
      d.Nodes := old(d.Nodes)[..iter.index] + [x] + old(d.Nodes)[iter.index..];
      d.Vals  := old(d.Vals) [..iter.index] + [v] + old(d.Vals) [iter.index..];
      d.Repr  := old(d.Repr) + {x};
    }
  }

  method RemoveIter<T>(d:PrivateDoublyLinkedList<T>, iter:DllIterator<T>) returns (good:bool)
    requires iter.Valid() && iter.d == d
    modifies d, d.Repr, iter
    ensures  d.Valid()
    ensures  good ==> iter.Valid();
    ensures !good ==> iter.GetIndex() == |d.Vals|
    ensures  iter.GetIndex() == old(iter.GetIndex()) && iter.d == d
    ensures  forall o :: o in d.Repr ==> o in old(d.Repr)
    ensures  d.Vals == old(d.Vals)[..old(iter.GetIndex())] + old(d.Vals)[old(iter.GetIndex())+1..]
  {
    good := iter.ptr.R != null;
    var tmp := iter.ptr.R;
    ghost var k := d.Remove(iter.ptr);
    if good {
      iter.ptr := tmp;
      iter.index := iter.index;
    }
  }

}
