// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/dafny/array-examples/standard_compare_ground.dfy
// SV-COMP array-examples/standard_compare_ground.yml (expected: safe), translated from the C program by hand: a and
// b are filled with arbitrary values and compared, a flag rv, initially 1, is reset where they differ, and if it is
// still set, they are equal
//
// findings: the comparison loop resets a flag where a and b differ; the flag lemma gives its final value, 1 iff the
// iteration constraint that a and b agree holds, which is abstracted by the auxiliary predicate agree_prefix(n, xs,
// ys) of teq.dfy and instantiated at the positions of the assertions by its lemma whose left-hand side is the atom
// earlier(j, xs) == earlier(j, ys); -split splits the conditional of the flag. Attempts: the iteration constraint
// itself as the side condition does not terminate, since matching it builds contexts in which the lemma applies to
// its body, and the equation of prefixes with an open length is not matched against the facts (see TODO.md); closed
// (no output)
// note: its lemmas are part of teq.dfy now (agree_prefix_def, earlier_agree_prefix) and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

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
