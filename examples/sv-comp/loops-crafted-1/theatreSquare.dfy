// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/theatreSquare.dfy
// SV-COMP loops-crafted-1/theatreSquare.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks n_stones1 == n_stones2

method correct_version(n: int, m: int, a: int) returns (result: int) {
  {
    var i: int;
    var j: int;
    var b: int;
    var l: int;
    var x: int;
    var y: int;
    i := 0;
    j := 0;
    b := 0;
    l := 0;
    while b < n {
      b := b + a;
      i := i + 1;
    }
    while l < m {
      l := l + a;
      j := j + 1;
    }
    x := 0;
    y := 0;
    while x < i {
      y := y + j;
      x := x + 1;
    }
    result := y;
    return;
  }
}

method student_version(n: int, m: int, a: int) returns (result: int) {
  {
    var i: int;
    var j: int;
    var b: int;
    var l: int;
    var x: int;
    var y: int;
    i := 0;
    j := 0;
    b := 0;
    l := 0;
    while b < n {
      b := b + a;
      i := i + 1;
    }
    while l < m {
      l := l + a;
      j := j + 1;
    }
    x := 0;
    y := 0;
    while x < i {
      y := y + j;
      x := x + 1;
    }
    result := y;
    return;
  }
}

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var tmp₄: int;
  {
    var a: int;
    var n: int;
    var m: int;
    var n_stones1: int;
    var n_stones2: int;
    tmp₁ := *;
    a := tmp₁;
    tmp₂ := *;
    n := tmp₂;
    tmp₃ := *;
    m := tmp₃;
    tmp₄ := *;
    n_stones2 := tmp₄;
    n_stones1 := n_stones2;
    if 1 <= n && 1 <= m && 1 <= a && n <= 109 && m <= 109 && a <= 109 {
      n_stones1 := correct_version(n, m, a);
      n_stones2 := student_version(n, m, a);
    }
    assert n_stones1 == n_stones2;
    result := 0;
    return;
  }
}
