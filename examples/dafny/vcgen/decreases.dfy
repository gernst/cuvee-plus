// ./Cuvee.sh -vcgen -z3 examples/dafny/vcgen/decreases.dfy
// expected: valid
// loops and recursive calls decrease their termination measure

method count(n: int) returns (k: int)
  requires 0 <= n
  ensures k == n
{
  k := 0;
  while k < n
    invariant k <= n
    decreases n - k
  {
    k := k + 1;
  }
}

method down(n: int) returns (k: int)
  requires 0 <= n
  ensures k == 0
  decreases n
{
  if n == 0 {
    k := 0;
  } else {
    k := down(n - 1);
  }
}

method skip(n: int) returns (k: int)
  requires 0 <= n
  ensures k == 0
{
  k := n;
  while 0 < k
    invariant 0 <= k
    decreases k
  {
    k := k - 1;
    if k % 2 == 0 {
      continue;
    }
  }
}
