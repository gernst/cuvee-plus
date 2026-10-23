// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-programs/copysome1-1.dfy
// SV-COMP array-programs/copysome1-1.yml (expected: safe), translated from the C program by
// hand: a1 and a2 are filled with arbitrary values, a1 is copied into a2 except at the position z, and they agree
// except at z
//
// findings: the index skips z in the loop of the copy, with the cases i + 1 and 150001 for i == 150000, which
// agree, but the simplifier has substituted the guard into the second; a lemma joins such cases into a counter,
// where the second result is a variable d with the side condition d == F(c), since F(c) would be compared
// literally; a lemma on guarded stores at the positions of a counter gives the reads; closed (no output)
// note: 2 of its lemmas are part of teq.dfy now and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 200000

method main() {
  var N: int;
  var a1: array<int, int>;
  var a2: array<int, int>;
  var i: int;
  var z: int;
  var x: int;
  var tmp: int;
  assume 0 < N;
  z := 150000;
  i := 0;
  while i < N {
    tmp := *;
    a1 := a1[i := tmp];
    tmp := *;
    a2 := a2[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if i != z {
      a2 := a2[i := a1[i]];
    }
    i := i + 1;
  }
  x := 0;
  while x < N {
    if x != z {
      assert a1[x] == a2[x];
    }
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
