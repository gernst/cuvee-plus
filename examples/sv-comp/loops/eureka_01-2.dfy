// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/eureka_01-2.dfy
// SV-COMP ReachSafety-Loops/loops/eureka_01-2.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks distance[i]>=0
// note: the concrete loop bounds are symbolic, arbitrary positive values: edgecount for 20

// the constant array of the initializers of C, whose values are all x
function constant(x: int): array<int, int>

lemma {:rw} {:teq} constant_1(x: int, i: int)
  ensures constant(x)[i] == x

var INFINITY: int;

method main() returns (result: int)
  modifies INFINITY
  requires INFINITY == 0
{
  INFINITY := 899;
  {
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
    nodecount := 5;
    edgecount := *;
    assume 0 < edgecount;
    source := 0;
    Source := constant(0)[0 := 0][1 := 4][2 := 1][3 := 1][4 := 0][5 := 0][6 := 1][7 := 3][8 := 4][9 := 4][10 := 2][11 := 2][12 := 3][13 := 0][14 := 0][15 := 3][16 := 1][17 := 2][18 := 2][19 := 3];
    Dest := constant(0)[0 := 1][1 := 3][2 := 4][3 := 1][4 := 1][5 := 4][6 := 3][7 := 4][8 := 3][9 := 0][10 := 0][11 := 0][12 := 0][13 := 2][14 := 3][15 := 0][16 := 2][17 := 1][18 := 0][19 := 4];
    Weight := constant(0)[0 := 0][1 := 1][2 := 2][3 := 3][4 := 4][5 := 5][6 := 6][7 := 7][8 := 8][9 := 9][10 := 10][11 := 11][12 := 12][13 := 13][14 := 14][15 := 15][16 := 16][17 := 17][18 := 18][19 := 19];
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
}
