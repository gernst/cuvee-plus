// ./Cuvee.sh -teq -simplify examples/sv-comp/array-lopstr16/flag_loopdep_simple.dfy
// SV-COMP ReachSafety-Arrays/array-lopstr16/flag_loopdep_simple.yml (expected: safe), translated from the C program by hand:
// the elements are arbitrary (the function init, inlined), the flag is set if one is not 0, and if it is not
// set, all are checked to be 0
//
// findings: a flag that is set whenever the read value is not 0 keeps its initial value iff it is never set, an
// iteration constraint, by a lemma generic in the condition; the constraint that the values are 0 is abstracted by
// the predicate constant, whose instantiation rewrites earlier(j, xs) to the constant; closed (no output)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀

// the first n values of xs are c, an auxiliary predicate, which is not defined
predicate constant(n: int, xs: seq<int>, c: int)

// a flag that is set to d whenever C holds, and kept otherwise, keeps its initial value x0 iff it is set to x0 or C
// never holds (with a further dependency hs)
lemma {:rw} {:free} {:teq} forall x0: int, d: int, n: int, hs: seq<int>, C: (int, int) -> bool ::
  current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do f, k, h :: case C(k, h) => d case !C(k, h) => f)) == x0
    <==> d == x0 || invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: !C(k, h))

// the iteration constraint that the values xs read at the iterations are c, abstracted by the predicate constant,
// and its instantiation at an iteration j before n, which rewrites the term earlier(j, xs)
lemma {:rw} {:free} {:teq} forall n: int, hs: seq<int>, xs: seq<int>, c: int ::
  invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: earlier(k, xs) == c) <==> constant(n, xs, c)
lemma {:rw} {:free} {:teq} forall n: int, xs: seq<int>, c: int, j: int ::
  if constant(n, xs, c) && 0 <= j < n
  then earlier(j, xs) == c

method main() {
  var i: int;
  var v: int;
  var flag: int;
  var a: array<int, int>;
  flag := 0;
  i := 0;
  while i < 1000000 {
    havoc v;
    a := a[i := v];
    i := i + 1;
  }
  i := 0;
  while i < 1000000 {
    if a[i] != 0 {
      flag := 1;
    }
    i := i + 1;
  }
  i := 0;
  while i < 1000000 {
    if flag == 0 {
      assert a[i] == 0;
    }
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
