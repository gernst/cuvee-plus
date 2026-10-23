// ./Cuvee.sh -hybrid -vcgen -prove examples/dafny/hybrid/clock.dfy
// a clock x that runs for at most 2 time units, after which the history ticks by the time that has passed,
// which is the value of the clock, hence the history has a single time event of at most 2,
// or none if no time has passed (see delay in resources/cuvee/dafny/hybrid.dfy)

var history: history<int>

method clock() returns (x: real)
  modifies history
  requires history.events == []
  ensures history.events == [] || exists s: real :: 0.0 < s <= 2.0 && history.events == [time(s)]
{
  x := 0.0;
  ode t :: x' == 1.0 while x <= 2.0
    invariant x == t;
}
