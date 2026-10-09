// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/nec11.dfy
// SV-COMP loops/nec11.yml (expected: unsafe), translated from the C program by ./Cuvee.sh -print
// dfy: a variant of nec20 with other constants or assertions; checks len==5

method main() returns (result: int) {
  var tmp₁: bool;
  var a: array<int, int>;
  var len: int;
  var c: bool;
  var i: int;
  len := 0;
  tmp₁ := *;
  c := tmp₁;
  while c {
    if len == 4 {
      len := 0;
    }
    a := a[len := 0];
    len := len + 1;
  }
  assert len == 5;
  result := 1;
  return;
}
