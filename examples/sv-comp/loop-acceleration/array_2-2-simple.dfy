// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/array_2-2-simple.dfy
// SV-COMP loop-acceleration/array_2-2-simple.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a variant of array_2-1-simple with other constants or assertions; checks A[2048/2] ==
// B[2048/2]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 2048

// the constant array of the initializers of C, whose values are all x
function constant(x: int): array<int, int>

lemma {:rw} {:teq} constant_1(x: int, i: int)
  ensures constant(x)[i] == x

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var A: array<int, int>;
    var B: array<int, int>;
    var i: int;
    var tmp: int;
    A := constant(0)[0 := 0];
    B := constant(0)[0 := 0];
    i := 0;
    while i < N {
      tmp := A[i];
      B := B[i := tmp];
      i := i + 1;
    }
    assert A[1024] == B[1024];
  }
}
