// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_strcmp_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_strcmp_ground.yml (expected: safe), translated from the C program by hand:
// _strcmp (inlined) returns 1 at the first position where a and b differ, and 0 otherwise, in which case they
// are checked to agree everywhere; the return from the loop is a break with the result
//
// findings: the comparison breaks at the first difference; -teq turns c == 0 into the iteration constraint that
// both agree, which the lemmas of standard_compare_ground abstract by agree and instantiate at the position; closed
// (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing; the lemmas are
// those of standard_compare_ground
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀

// two sequences agree at the positions 0, ..., n - 1, an auxiliary predicate, which is not defined
predicate agree(n: int, xs: seq<int>, ys: seq<int>)

// two sequences that are equal at all iterations 0, ..., n - 1 agree there, and then at each position j in that range;
// the instantiation needs agree, since a side condition invs(... earlier(k, xs) == earlier(k, ys)) would be matched
// in a context, in which the lemma applies to its body, and an equation of prefixes prefix(n, xs) == prefix(n, ys)
// with n open is not matched against the facts (see TODO.md); the atom is stated as such, since an equation of
// integers would be a rule on its left-hand side as a term
lemma {:rw} {:free} {:teq} forall n: int, xs: seq<int>, ys: seq<int>, hs: seq<int> ::
  invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: earlier(k, xs) == earlier(k, ys)) <==> agree(n, xs, ys)
lemma {:rw} {:free} {:teq} forall n: int, j: int, xs: seq<int>, ys: seq<int> ::
  if agree(n, xs, ys) && 0 <= j < n
  then (earlier(j, xs) == earlier(j, ys)) <==> true

method main() {
  var i: int;
  var x: int;
  var v: int;
  var c: int;
  var a: array<int, int>;
  var b: array<int, int>;
  i := 0;
  while i < 100000 {
    v := *;
    a := a[i := v];
    v := *;
    b := b[i := v];
    i := i + 1;
  }
  c := 0;
  i := 0;
  while i < 100000 {
    if b[i] != a[i] {
      c := 1;
      break;
    }
    i := i + 1;
  }
  if c == 0 {
    x := 0;
    while x < 100000 {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// none
