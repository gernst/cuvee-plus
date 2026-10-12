// ./Cuvee.sh -vcgen -z3 examples/dafny/vcgen/contract.dfy
// expected: valid
// calls to methods without body rely on their contract only

type counter {
  function get(): int

  method inc() returns (that: counter)
    ensures that.get() == this.get() + 1
}

method twice(c: counter) returns (d: counter)
  ensures d.get() == c.get() + 2
{
  var e: counter;
  e := c.inc();
  d := e.inc();
}
