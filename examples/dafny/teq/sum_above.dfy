// ./Cuvee.sh -teq -include teq:aggregation -prove examples/dafny/teq/sum_above.dfy
// a sum of values chosen by cases on a value of each iteration, all positive, is positive after an iteration (like
// loop-invgen/large_const of SV-COMP): the values are a map with cases over the counter and the choices, which
// sum_above bounds case by case; in the wrong version one case adds 0, which remains

method positive(N: int) returns (S: int)
  requires 0 < N
  ensures 0 < S
{
  var i: int;
  var v: int;
  S := 0;
  i := 0;
  while i < N
  {
    v := *;
    if v == 0 { S := S + 4000; } else if v == 1 { S := S + 2000; } else { S := S + 10000; }
    i := i + 1;
  }
}

method positive_wrong(N: int) returns (S: int)
  requires 0 < N
  ensures 0 < S
{
  var i: int;
  var v: int;
  S := 0;
  i := 0;
  while i < N
  {
    v := *;
    if v == 0 { S := S + 4000; } else if v == 1 { S := S + 0; } else { S := S + 10000; }
    i := i + 1;
  }
}
