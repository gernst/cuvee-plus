// ./Cuvee.sh -teq -prove examples/dafny/teq/break_once.dfy
// a loop whose body ends by break or return on all paths runs it at most once, as a conditional, without a trace
// equation system: a path that ends by break continues after the loop, one that ends by return leaves the method

method once() {
  var x: int;
  x := 1;
  while true {
    x := 0;
    break;
  }
  assert x == 0;
}

method early(n: int) returns (r: int)
  ensures r == 0 || r == 1
{
  r := 0;
  while 0 < n {
    if n == 1 {
      r := 1;
      return;
    }
    break;
  }
  assert r == 0;
}
