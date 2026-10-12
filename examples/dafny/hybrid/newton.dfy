// ./Cuvee.sh -vcgen -simplify examples/dafny/hybrid/newton.dfy
// newton's law of motion under a constant acceleration a: the closed forms of velocity and position
// with respect to the time t of the differential equation, starting from x0 and v0, as differential invariants;
// the invariant of the position follows by the differential cut with the one of the velocity
method newton(a: real, x0: real, v0: real) returns (x: real, v: real)
{
  x, v := x0, v0;
  ode t :: x', v' == v, a
    invariant v == v0 + a * t
    invariant 2.0 * x == 2.0 * x0 + 2.0 * v0 * t + a * t * t;
}
