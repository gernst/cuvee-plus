// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/data_structures_set_multi_proc_trivial_ground.dfy
// SV-COMP array-examples/data_structures_set_multi_proc_trivial_ground.yml (expected: safe),
// translated from the C program by ./Cuvee.sh -print dfy: a program of the folder; checks set[ x ] != set[ y ];
// set[ x ] != set[ y ]; set[ x ] != set[ y ]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

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

method main() returns (result: int) {
  var N: int;
  var tmp₂: int;
  var tmp₃: int;
  var tmp₄: int;
  var n: int;
  var set: array<int, int>;
  var x: int;
  var y: int;
  var values: array<int, int>;
  var v: int;
  assume 0 < N;
  n := 0;
  x := 0;
  while x < N {
    tmp₂ := *;
    set := set[x := tmp₂];
    x := x + 1;
  }
  x := 0;
  while x < n {
    y := x + 1;
    while y < n {
      assert set[x] != set[y];
      y := y + 1;
    }
    x := x + 1;
  }
  v := 0;
  while v < N {
    tmp₃ := *;
    values := values[v := tmp₃];
    v := v + 1;
  }
  v := 0;
  while v < N {
    tmp₄ := elem_exists(set, n, values[v]);
    if (tmp₄ != 0) {
      n := insert(set, n, values[v]);
    }
    x := 0;
    while x < n {
      y := x + 1;
      while y < n {
        assert set[x] != set[y];
        y := y + 1;
      }
      x := x + 1;
    }
    v := v + 1;
  }
  x := 0;
  while x < n {
    y := x + 1;
    while y < n {
      assert set[x] != set[y];
      y := y + 1;
    }
    x := x + 1;
  }
  result := 0;
  return;
}
