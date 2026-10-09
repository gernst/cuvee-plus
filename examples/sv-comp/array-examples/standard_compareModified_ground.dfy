// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-examples/standard_compareModified_ground.dfy
// SV-COMP array-examples/standard_compareModified_ground.yml (expected: safe), translated from the C program by hand:
// a flag rv is cleared if a and b differ at some position, while a is copied into c; if rv is still set, a and
// b are checked to agree, and c is checked to agree with a
//
// findings: as standard_password_ground, with the copy c of a, which teq.dfy reads back; closed (no output) with
// the lemmas of teq.dfy on agree_prefix and -split
// note: its lemmas are part of teq.dfy now (agree_prefix_def, earlier_agree_prefix) and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var j: int;
  var x: int;
  var v: int;
  var rv: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  assume 0 < N;
  i := 0;
  rv := 1;
  j := 0;
  while j < N {
    v := *;
    a := a[j := v];
    v := *;
    b := b[j := v];
    j := j + 1;
  }
  while i < N {
    if a[i] != b[i] {
      rv := 0;
    }
    c := c[i := a[i]];
    i := i + 1;
  }
  if rv != 0 {
    x := 0;
    while x < N {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
  x := 0;
  while x < N {
    assert a[x] == c[x];
    x := x + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
