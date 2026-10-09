// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/array_1-1.dfy
// SV-COMP loop-acceleration/array_1-1.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of array_1-2 with other constants or assertions; checks A[1023] != 1023
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1024

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var A: array<int, int>;
    var i: int;
    i := 0;
    while i < N {
      A := A[i := i];
      i := i + 1;
    }
    assert A[1023] != 1023;
  }
}
