// ./Cuvee.sh -teq -entry lsearch -split -simplify examples/dafny/algorithms/lsearch.dfy
// linear search: the first index of x among the first n elements of a, n if there is none
//
// status: verified with -teq -split -simplify; without -split, the goal that remains is the disjunction of the
// exits, which holds by a case split on a[i] == x that the simplifier does not make;
// the iteration constraint a[k] != x over the counter becomes !occurs(x, selects(a, ⌊counter(0, 1, n)⌋)) by the
// first lemma, like not_occurs_prefix_def of teq.dfy for reads earlier(k, xs), and the second lemma instantiates it
// at the index k of the postcondition, which turns the hypothesis a[k] == x of the split goal into false

// the iterations before the exit do not find x: x does not occur among the values of a at the positions visited
lemma {:rw} not_occurs_selects_def(a: array<int, int>, x: int, i: int, n: Nat)
  ensures invs(for ⌊counter(i, 1, n)⌋ check k :: a[k] != x) <==> !occurs(x, selects(a, ⌊counter(i, 1, n)⌋))

// which is instantiated at the positions k in that range
lemma {:rw} select_not_occurs_selects(a: array<int, int>, x: int, i: int, n: Nat, k: int)
  requires !occurs(x, selects(a, ⌊counter(i, 1, n)⌋)) && i <= k < i + integer(n)
  ensures (a[k] == x) <==> false

method lsearch(a: array<int, int>, n: int, x: int) returns (i: int)
  requires 0 <= n
  ensures 0 <= i <= n
  ensures i < n ==> a[i] == x
  ensures forall k: int :: 0 <= k < i ==> a[k] != x
{
  i := 0;
  while i < n && a[i] != x
  {
    i := i + 1;
  }
}
