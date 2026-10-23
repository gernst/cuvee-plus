// ./Cuvee.sh -teq -include teq:sorted -prove examples/dafny/algorithms/perm.dfy
// permutations by swaps in single loops: a reversal of a[0..n), and swaps with arbitrary positions
//
// status: verified with the lemmas of teq:sorted alone (Oct 23, 2026; formerly with local copies of perm_refl,
// perm_swap and perm_swaps);
// perm(a, b) is an abstract predicate, a is a permutation of b as a total map on the indices, which a swap preserves,
// and a trace of swaps too, whose positions P and Q may depend on the state and on the iteration (a higher-order
// pattern, bound like the cases of incs in bsearch.dfy); the goal perm(current(trace(...)), a) becomes perm(a, a)

method reverse(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures perm(b, a)
{
  var i: int;
  var t: int;
  b := a;
  i := 0;
  while i < n - 1 - i
  {
    t := b[i];
    b[i] := b[n - 1 - i];
    b[n - 1 - i] := t;
    i := i + 1;
  }
}

method shuffle(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures perm(b, a)
{
  var i: int;
  var m: int;
  var t: int;
  b := a;
  i := 0;
  while i < n
  {
    m := *;
    t := b[i];
    b[i] := b[m];
    b[m] := t;
    i := i + 1;
  }
}
