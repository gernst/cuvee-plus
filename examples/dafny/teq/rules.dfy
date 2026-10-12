// ./Cuvee.sh -teq -simplify -rules examples/dafny/teq/rules.dfy
// the rules that -simplify applies to each goal, by their names (:named of the lemmas, the functions of definitions):
// as (set-info :used ((name count) ...)) after each goal, also after those that simplify to true and are dropped

// closed by the lemmas on counters, stores, and selects
method copy(a: array<int, int>, n: int) returns (b: array<int, int>)
  requires 0 <= n
  ensures forall k: int :: 0 <= k < n ==> b[k] == a[k]
{
  var i: int;
  i := 0;
  while i < n {
    b[i] := a[i];
    i := i + 1;
  }
}

// remains, with the count of the negative entries
method count(a: array<int, int>, n: int) returns (c: int)
  requires 0 <= n
  ensures c <= n
{
  var i: int;
  i := 0;
  c := 0;
  while i < n {
    if a[i] < 0 {
      c := c + 1;
    }
    i := i + 1;
  }
}
