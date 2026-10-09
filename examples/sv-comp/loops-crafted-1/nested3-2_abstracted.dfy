// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/nested3-2_abstracted.dfy
// SV-COMP loops-crafted-1/nested3-2_abstracted.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of nested3-1_abstracted with other constants or assertions; checks
// !(z % 4); !(y % 2); !(x % 2)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 268435455

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

// the remainder of C, which truncates towards zero
function {:rw} remainder(a: int, b: int): int { if 0 <= a then a % b else -((-a) % b) }

method main() returns (result: int) {
  var N: int;
  assume 0 < N;
  {
    var x: int;
    var y: int;
    var z: int;
    var w: int;
    x := 0;
    y := 0;
    z := 0;
    w := 0;
    while x < N {
      y := 0;
      while y < N {
        z := 0;
        if z < N {
          var z__VERIFIER_LA_tmp0: int;
          var __VERIFIER_LA_iterations0: int;
          var z__VERIFIER_LA_old_tmp0: int;
          z__VERIFIER_LA_tmp0 := z;
          __VERIFIER_LA_iterations0 := (quotient(N - z__VERIFIER_LA_tmp0, 1));
          z__VERIFIER_LA_old_tmp0 := z;
          z := __VERIFIER_LA_iterations0 * 1 + z__VERIFIER_LA_old_tmp0;
        }
        assert !(((remainder(z, 4))) != 0);
        y := y + 1;
      }
      assert !(((remainder(y, 2))) != 0);
      x := x + 1;
    }
    assert !(((remainder(x, 2))) != 0);
    result := 0;
    return;
  }
}
