// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-examples/standard_compareModified_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_compareModified_ground.yml (expected: safe), translated from the C program by hand:
// a flag rv is cleared if a and b differ at some position, while a is copied into c; if rv is still set, a and
// b are checked to agree, and c is checked to agree with a
//
// findings: as standard_password_ground, with the copy c of a, which teq.dfy reads back; closed (no output) with
// the lemmas of standard_compare_ground and -split
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
  var j: int;
  var x: int;
  var v: int;
  var rv: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  i := 0;
  rv := 1;
  j := 0;
  while j < 100000 {
    havoc v;
    a := a[j := v];
    havoc v;
    b := b[j := v];
    j := j + 1;
  }
  while i < 100000 {
    if a[i] != b[i] {
      rv := 0;
    }
    c := c[i := a[i]];
    i := i + 1;
  }
  if rv != 0 {
    x := 0;
    while x < 100000 {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  x := 0;
  while x < 100000 {
    assert a[x] == c[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
