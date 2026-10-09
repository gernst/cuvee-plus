// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-new/count_by_nondet.dfy
// SV-COMP ReachSafety-Loops/loop-new/count_by_nondet.yml (expected: safe), translated from the C program by hand: i
// increases by an arbitrary step j between 1 and 999999 until it reaches 1000000, k counts the iterations, which
// are at most 1000000
//
// findings: i adds arbitrary steps j of at least 1, its trace is sums(0, J) of their sequence; the iteration
// constraints, the loop test i < b before each iteration and the bound 1 <= j of the steps, are abstracted by
// auxiliary predicates below and positive, of which a third lemma concludes n <= b, i.e., at most b iterations, for
// 0 <= b, by a left-hand side that is a comparison, with atoms as side conditions; the order of the abstractions
// matters, since positive also matches the loop test, with the map of b - i as its sequence; closed (no output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function sums(x: int, values: seq<int>): Trace<int>

// the first n values of js are at least 1, and the partial sums of js before each of the first n values are below b,
// auxiliary predicates, which are not defined
predicate positive(n: int, js: seq<int>)
predicate below(n: int, js: seq<int>, b: int)

// the iteration constraints of a loop that adds the values js, i.e., its value is sums(0, js), abstracted by these
// predicates: the loop test, a bound b on the value, held before each iteration, and the values are at least 1;
// the bound comes first, since rules apply in their order, and the second one matches the bound as well, where the
// plain dependency js is the map of b - i
lemma {:rw} {:free} {:teq} forall n: int, b: int, js: seq<int>, hs: seq<int> ::
  invs(for ⌊counter(0, 1, n)⌋, ⌊sums(0, js)⌋, hs check k, i, h :: i < b) <==> below(n, js, b)
lemma {:rw} {:free} {:teq} forall n: int, js: seq<int>, hs: seq<int> ::
  invs(for ⌊counter(0, 1, n)⌋, hs, js check k, h, j :: 1 <= j) <==> positive(n, js)

// with steps of at least 1, the partial sum before the last of n iterations is at least n - 1, and below b, hence
// there are at most b iterations, also none for 0 <= b; the left-hand side is a comparison, whose side conditions
// are atoms
lemma {:rw} {:free} {:teq} forall n: int, b: int, js: seq<int> ::
  if positive(n, js) && below(n, js, b) && 0 <= b
  then n <= b

method main() {
  var i: int;
  var k: int;
  var j: int;
  i := 0;
  k := 0;
  while i < 1000000 {
    j := *;
    assume 1 <= j < 1000000;
    i := i + j;
    k := k + 1;
  }
  assert k <= 1000000;
}

// remaining goals of -teq -simplify:
// none
