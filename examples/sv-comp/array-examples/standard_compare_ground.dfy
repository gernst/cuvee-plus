// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-examples/standard_compare_ground.dfy
// SV-COMP array-examples/standard_compare_ground.yml (expected: safe), translated from the C
// program by hand: a and b are filled with arbitrary values and compared, a flag rv, initially 1, is reset where
// they differ, and if it is still set, they are equal
//
// findings: the comparison loop resets a flag where a and b differ; the flag lemma gives its final value, 1 iff the
// iteration constraint that a and b agree holds, which is abstracted by the auxiliary predicate agree(n, xs, ys)
// and instantiated at the positions of the assertions by a lemma whose left-hand side is the atom earlier(j, xs) ==
// earlier(j, ys); -split splits the conditional of the flag. Attempts: the iteration constraint itself as the side
// condition does not terminate, since matching it builds contexts in which the lemma applies to its body, and the
// equation of prefixes with an open length is not matched against the facts (see TODO.md); closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
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
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var rv: int;
  var x: int;
  var tmp: int;
  assume 0 < N;
  i := 0;
  while i < N {
    tmp := *;
    a := a[i := tmp];
    tmp := *;
    b := b[i := tmp];
    i := i + 1;
  }
  i := 0;
  rv := 1;
  while i < N {
    if a[i] != b[i] {
      rv := 0;
    }
    i := i + 1;
  }
  if rv != 0 {
    x := 0;
    while x < N {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
