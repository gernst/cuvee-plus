// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-examples/standard_password_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_password_ground.yml (expected: safe), translated from the C program by hand:
// a flag result is cleared if password and guess differ at some position, and if it is still set, they are
// checked to agree everywhere
//
// findings: the flag result, cleared at a difference, is summarized by the flag lemma of standard_compare_ground as
// (if agree(100000, ...) then 1 else 0), whose constraint agree is instantiated at the position; -split splits the
// hypotheses result == (if ...) and result != 0, as for standard_compare_ground; closed (no output); with -teq
// -simplify alone, the hypotheses are not reduced to agree(...), since the branches of a conditional formula are
// not simplified under the facts, and a lemma that splits the equation of a conditional cannot be combined with
// -split, which splits that lemma, too (see TODO.md)
// note: 1 of its lemmas are part of teq.dfy now and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

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
lemma {:rw} {:teq} invs_1(n: int, xs: seq<int>, ys: seq<int>, hs: seq<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: earlier(k, xs) == earlier(k, ys)) <==> agree(n, xs, ys)
lemma {:rw} {:teq} earlier_1(n: int, j: int, xs: seq<int>, ys: seq<int>)
  requires agree(n, xs, ys) && 0 <= j < n
  ensures (earlier(j, xs) == earlier(j, ys)) <==> true

method main() {
  var N: int;
  var i: int;
  var x: int;
  var v: int;
  var result: int;
  var password: array<int, int>;
  var guess: array<int, int>;
  assume 0 < N;
  result := 1;
  i := 0;
  while i < N {
    v := *;
    password := password[i := v];
    v := *;
    guess := guess[i := v];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if password[i] != guess[i] {
      result := 0;
    }
    i := i + 1;
  }
  if result != 0 {
    x := 0;
    while x < N {
      assert password[x] == guess[x];
      x := x + 1;
    }
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
