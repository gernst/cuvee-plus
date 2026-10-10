// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-industry-pattern/check_removal_from_set_after_insertion.dfy
// SV-COMP array-industry-pattern/check_removal_from_set_after_insertion.yml (expected: unsafe),
// translated from the C program by ./Cuvee.sh -print dfy: a program of the folder; checks set[i] != element
// note: the concrete loop bounds are symbolic, arbitrary positive values: SIZE for 100000

var SIZE: int;

method insert(set: array<int, int>, size: int,
              value: int) returns (result: int) {
  var set₁: array<int, int>;
  set₁ := set;
  set₁ := set₁[size := value];
  result := size + 1;
  return;
}

method elem_exists(set: array<int, int>, size: int,
                   value: int) returns (result: int) {
  {
    var i: int;
    i := 0;
    while i < size {
      if set[i] == value {
        result := 1;
        return;
      }
      i := i + 1;
    }
    result := 0;
    return;
  }
}

method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0
{
  var tmp₂: int;
  var tmp₃: int;
  var tmp₄: int;
  var i: int;
  var pos: int;
  var n: int;
  var found: int;
  var set: array<int, int>;
  var values: array<int, int>;
  var element: int;
  var v: int;
  SIZE := *;
  assume 0 < SIZE;
  n := 0;
  found := 0;
  i := 0;
  while i < SIZE {
    tmp₂ := *;
    set := set[i := tmp₂];
    tmp₃ := *;
    values := values[i := tmp₃];
    i := i + 1;
  }
  element := *;
  v := 0;
  while v < SIZE {
    tmp₄ := elem_exists(set, n, values[v]);
    if tmp₄ != 1 {
      n := insert(set, n, values[v]);
    }
    v := v + 1;
  }
  i := 0;
  while i < SIZE && found != 1 {
    if set[i] == element {
      found := 1;
      pos := i;
    }
    i := i + 1;
  }
  if found == 1 {
    i := pos;
    while i < SIZE - 1 {
      set := set[i := set[i + 1]];
      i := i + 1;
    }
  }
  if found == 1 {
    i := 0;
    while i < SIZE - 1 {
      assert set[i] != element;
      i := i + 1;
    }
  }
}
