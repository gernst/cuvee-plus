// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops/eureka_01-2.dfy
// SV-COMP loops/eureka_01-2.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks distance[i]>=0
// note: the concrete loop bounds are symbolic, arbitrary positive values: edgecount for 20
// note: the edges of the C program, constant arrays, are arbitrary, filled by a loop, with nodes below nodecount
// and nonnegative weights, as there

method main() returns (result: int) {
  var INFINITY: int;
  var nodecount: int;
  var edgecount: int;
  var source: int;
  var Source: array<int, int>;
  var Dest: array<int, int>;
  var Weight: array<int, int>;
  var distance: array<int, int>;
  var x: int;
  var y: int;
  var i: int;
  var j: int;
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  INFINITY := 899;
  nodecount := 5;
  edgecount := *;
  assume 0 < edgecount;
  source := 0;
  i := 0;
  while i < edgecount {
    tmp₁ := *;
    assume 0 <= tmp₁ < nodecount;
    Source := Source[i := tmp₁];
    tmp₂ := *;
    assume 0 <= tmp₂ < nodecount;
    Dest := Dest[i := tmp₂];
    tmp₃ := *;
    assume 0 <= tmp₃;
    Weight := Weight[i := tmp₃];
    i := i + 1;
  }
  i := 0;
  while i < nodecount {
    if i == source {
      distance := distance[i := 0];
    } else {
      distance := distance[i := INFINITY];
    }
    i := i + 1;
  }
  i := 0;
  while i < nodecount {
    j := 0;
    while j < edgecount {
      x := Dest[j];
      y := Source[j];
      if distance[x] > distance[y] + Weight[j] {
        distance := distance[x := distance[y] + Weight[j]];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  i := 0;
  while i < edgecount {
    x := Dest[i];
    y := Source[i];
    if distance[x] > distance[y] + Weight[i] {
      result := 0;
      return;
    }
    i := i + 1;
  }
  i := 0;
  while i < nodecount {
    assert distance[i] >= 0;
    i := i + 1;
  }
  result := 0;
  return;
}
