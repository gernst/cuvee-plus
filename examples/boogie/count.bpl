// expected: valid
// loops with invariants, calls with and without results

procedure count(n: int) returns (k: int)
  requires 0 <= n;
  ensures k == n;
{
  k := 0;
  while (k < n)
    invariant k <= n;
  {
    var l: int;
    l := k + 1;
    k := l;
  }
}

procedure twice(n: int) returns (k: int)
  requires 0 <= n;
  ensures k == 2 * n;
{
  var i: int, j: int;
  call i := count(n);
  call j := count(n);
  k := i + j;
}

procedure validate(n: int);
  requires 0 <= n;

procedure caller()
{
  call validate(1);
}
