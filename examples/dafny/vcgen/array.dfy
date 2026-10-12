// ./Cuvee.sh -vcgen -z3 examples/dafny/vcgen/array.dfy
// expected: valid
// SMT-LIB arrays

method update(m: array<int,int>, i: int, j: int) returns (n: array<int,int>)
  requires i != j
  ensures n[i] == 1
  ensures n[j] == m[j]
{
  n := m[i := 1];
}
