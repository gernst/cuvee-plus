// ./Cuvee.sh -vcgen -z3 examples/dafny/vcgen/old.dfy
// expected: valid
// global variables, which are not Dafny, and old(e) for their values at the entry of a method

var count: int;

method inc(n: int)
  modifies count
  requires 0 <= n
  ensures count == old(count) + n
{
  count := count + n;
}

method twice(n: int)
  modifies count
  requires 0 <= n
  ensures old(count) <= count && count == old(count + 2 * n)
{
  inc(n);
  inc(n);
}

method loop(n: int)
  modifies count
  requires 0 <= n
  ensures count == old(count) + n
{
  var i: int;
  i := 0;
  while i < n
    modifies count
    invariant i <= n && count == old(count) + i
  {
    inc(1);
    i := i + 1;
  }
}
