// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/dafny/array-examples/standard_password_ground.dfy
// SV-COMP array-examples/standard_password_ground.yml (expected: safe), translated from the C program by hand:
// a flag result is cleared if password and guess differ at some position, and if it is still set, they are
// checked to agree everywhere
//
// findings: the flag result, cleared at a difference, is summarized by the flag lemma of teq.dfy as (if
// agree_prefix(N, ...) then 1 else 0), whose constraint agree_prefix is instantiated at the position; -split splits the
// hypotheses result == (if ...) and result != 0, as for standard_compare_ground; closed (no output); with -teq
// -simplify alone, the hypotheses are not reduced to agree_prefix(...), since the branches of a conditional formula are
// not simplified under the facts, and a lemma that splits the equation of a conditional cannot be combined with
// -split, which splits that lemma, too (see TODO.md)
// note: its lemmas are part of teq.dfy now (agree_prefix_def, earlier_agree_prefix) and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

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
