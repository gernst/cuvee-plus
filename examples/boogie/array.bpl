// ./Cuvee.sh -verify -monomorph -z3 examples/boogie/array.bpl
// expected: valid
// maps as SMT-LIB arrays, selection, update, and assignment to an element

var mem: [int]int;

procedure write(p: int, v: int)
  ensures mem[p] == v;
  modifies mem;
{
  mem[p] := v;
}

procedure swap(a: [int]int, i: int, j: int) returns (b: [int]int)
  ensures b[i] == a[j] && b[j] == a[i];
{
  b := a[i := a[j]][j := a[i]];
}

procedure matrix(m: [int][int]bool) returns (n: [int][int]bool)
  ensures n[0][1];
{
  n := m;
  n[0][1] := true;
}
