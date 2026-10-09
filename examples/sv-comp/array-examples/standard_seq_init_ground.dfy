// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-examples/standard_seq_init_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_seq_init_ground.yml (expected: safe), translated from the C
// program by hand: a[0] is 7 and each further element is its predecessor plus 1, hence a is increasing
//
// findings: the array is filled by a recurrence, each element from its predecessor; the lemma gives its closed form
// at the positions of the counter (a0[0] + j * c), which is not an unfolding of the iterations; the result contains
// conditionals in atoms, which -split splits, and the second -simplify closes the cases (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var a: array<int, int>;
  var i: int;
  var x: int;
  assume 0 < N;
  i := 1;
  a := a[0 := 7];
  while i < N {
    a := a[i := a[i - 1] + 1];
    i := i + 1;
  }
  x := 1;
  while x < N {
    assert a[x] >= a[x - 1];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
