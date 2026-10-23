// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops-crafted-1/nested_delay_notd2.dfy
// SV-COMP loops-crafted-1/nested_delay_notd2.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a program of the folder; checks a==b && c==SIZE
// note: the concrete loop bounds are symbolic, arbitrary positive values: SIZE for 20

var last: int;

var SIZE: int;

method main() returns (result: int)
  modifies SIZE, last
  requires last == 0 && SIZE == 0
{
  var a: int;
  var b: int;
  var c: int;
  var st: int;
  var d: int;
  SIZE := *;
  assume 0 < SIZE;
  last := *;
  assume last > 0;
  a := 0;
  b := 0;
  c := 0;
  st := 0;
  d := 0;
  while (1 != 0) {
    st := 1;
    c := 0;
    while c < SIZE {
      if c >= last {
        st := 0;
      }
      c := c + 1;
    }
    if st == 0 && c == last + 1 {
      a := a + 3;
      b := b + 3;
    } else {
      a := a + 2;
      b := b + 2;
    }
    if c == last && st == 0 {
      a := a + 1;
    } else if st == 1 && last >= SIZE {
      d := d + 1;
    }
    if d == SIZE {
      a := 0;
      b := 1;
    }
    assert a == b && c == SIZE;
  }
  result := 0;
  return;
}
