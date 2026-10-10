// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/nec40.dfy
// SV-COMP loops/nec40.yml (expected: safe), translated from the C program by ./Cuvee.sh -print
// dfy: a variant of nec11 with other constants or assertions; checks 0

// the constant array of the initializers of C, whose values are all x
function {:c} constant(x: int): array<int, int>

lemma {:rw} {:teq} constant_1(x: int, i: int)
  ensures constant(x)[i] == x

var x: array<int, int>;

var y: array<int, int>;

var i: int;

var j: int;

var k: int;

method main() returns (result: int)
  modifies i, k, y
  requires x == constant(0) && y == constant(0) && i == 0 && j == 0 && k == 0
{
  k := *;
  i := 0;
  while x[i] != 0
    modifies i, y
  {
    y := y[i := x[i]];
    i := i + 1;
  }
  y := y[i := 0];
  if k >= 0 && k < i {
    if y[k] != 0 {
      assert (0 != 0);
    }
  }
  result := 0;
  return;
}
