// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-invgen/heapsort.dfy
// SV-COMP loop-invgen/heapsort.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks 1 <= j; j <= n; 1 <= j+1; j+1 <= n; 1 <= j; j <= n; 1 <= i; i <= n; 1
// <= j; j <= n; 1 <= l; l <= n; 1 <= r; r <= n

// the division of C, which truncates towards zero
function {:rw} quotient(a: int, b: int): int { if 0 <= a then a / b else -((-a) / b) }

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var n: int;
  var l: int;
  var r: int;
  var i: int;
  var j: int;
  n := *;
  if !(1 <= n) {
    result := 0;
    return;
  }
  l := (quotient(n, 2)) + 1;
  r := n;
  if l > 1 {
    l := l - 1;
  } else {
    r := r - 1;
  }
  while r > 1 {
    i := l;
    j := 2 * l;
    while j <= r {
      if j < r {
        assert 1 <= j;
        assert j <= n;
        assert 1 <= j + 1;
        assert j + 1 <= n;
        tmp₁ := *;
        if (tmp₁ != 0) {
          j := j + 1;
        }
      }
      assert 1 <= j;
      assert j <= n;
      tmp₂ := *;
      if (tmp₂ != 0) {
        break;
      }
      assert 1 <= i;
      assert i <= n;
      assert 1 <= j;
      assert j <= n;
      i := j;
      j := 2 * j;
    }
    if l > 1 {
      assert 1 <= l;
      assert l <= n;
      l := l - 1;
    } else {
      assert 1 <= r;
      assert r <= n;
      r := r - 1;
    }
  }
  result := 0;
  return;
}
