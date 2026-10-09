// ./Cuvee.sh -teq -simplify examples/sv-comp/loops-crafted-1/watermelon.dfy
// SV-COMP loops-crafted-1/watermelon.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks is_divisible1 == is_divisible2

var true: int;

var false: int;

method correct_version(w: int) returns (result: int) {
  {
    var is_divisible: int;
    is_divisible := true;
    if w < 4 {
      is_divisible := false;
    } else {
      var i: int;
      i := 0;
      while i < w {
        {}
        i := i + 2;
      }
      if i != w {
        is_divisible := false;
      }
    }
    result := is_divisible;
    return;
  }
}

method student_version(w: int) returns (result: int) {
  {
    var is_divisible: int;
    is_divisible := true;
    if w < 4 {
      is_divisible := false;
    } else {
      var i: int;
      i := 0;
      while i < w {
        {}
        i := i + 2;
      }
      if i != w {
        is_divisible := false;
      }
    }
    result := is_divisible;
    return;
  }
}

method main() returns (result: int)
  modifies false, true
  requires true == 0 && false == 0
{
  var tmp₁: int;
  true := 1;
  false := 0;
  {
    var w: int;
    var is_divisible1: int;
    var is_divisible2: int;
    tmp₁ := *;
    assume 0 <= tmp₁;
    w := tmp₁;
    is_divisible1 := true;
    is_divisible2 := true;
    if w > 0 && w < 10000000 {
      is_divisible1 := correct_version(w);
      is_divisible2 := student_version(w);
      assert is_divisible1 == is_divisible2;
    }
    result := 0;
    return;
  }
}
