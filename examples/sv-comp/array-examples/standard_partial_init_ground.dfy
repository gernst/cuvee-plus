// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_partial_init_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_partial_init_ground.yml (expected: safe), translated from the
// C program by hand: A and B are filled with arbitrary values, the indices where they agree are collected in C,
// counted by j, and each entry C[x] lies between x and x + i - j, i.e., the indices are increasing
//
// findings: rewriting does not terminate (a stack overflow, reported as such) with the lemmas of teq.dfy alone: the
// counter j of the agreeing indices is a count over a map whose dependency is ⌊I⌋, and the read earlier(k, ⌊J⌋)
// becomes a count over a prefix of that map, whose simplification binds a fresh k and builds the context of the
// iterations again, in which earlier(k', ⌊I⌋) is simplified, and so on (k₁₁₉ and growing); no lemma is added, since
// the assertions need a description of the stores at the positions given by the count, i.e., C[x] is the x-th index
// where A and B agree, whose concept (a selection of indices, monotone in x) is not in the database

method main() {
  var A: array<int, int>;
  var B: array<int, int>;
  var C: array<int, int>;
  var i: int;
  var j: int;
  var x: int;
  var tmp: int;
  j := 0;
  i := 0;
  while i < 100000 {
    tmp := *;
    A := A[i := tmp];
    tmp := *;
    B := B[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    if A[i] == B[i] {
      C := C[j := i];
      j := j + 1;
    }
    i := i + 1;
  }
  x := 0;
  while x < j {
    assert C[x] <= x + i - j;
    x := x + 1;
  }
  x := 0;
  while x < j {
    assert C[x] >= x;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// error "rewriting does not terminate"
//   the rule earlier(k, ⌊counter(i, c, n)⌋) == i + k * c of teq.dfy (printed as Rule(...), shortened here)
