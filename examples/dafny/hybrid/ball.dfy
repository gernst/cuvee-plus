// ./Cuvee.sh -verify -simplify examples/dafny/hybrid/ball.dfy
// hybrid programs: nondeterministic iterations, differential equations over a local time t with evolution constraints and
// differential invariants, and derivatives (x, y :: e)' of e with respect to x and y, which are on real

// a bouncing ball at height x with velocity v under gravity g
method ball(g: real, h: real) returns (x: real, v: real)
  requires 0.0 < g && 0.0 <= h
{
  x, v := h, 0.0;
  while *
    invariant 0.0 <= x && 2.0 * g * x + v * v <= 2.0 * g * h
  {
    ode t :: x', v' == v, -g while 0.0 <= x
      invariant 2.0 * g * x + v * v <= 2.0 * g * h;
    if x == 0.0 {
      v := -v;
    }
  }
}

// the derivative of the energy, which vanishes along the trajectories of the ball
method energy(g: real, h: real) returns (e: real)
{
  var x: real, v: real;
  x, v := h, 0.0;
  ode t :: x', v' == v, -g;
  e := (x, v :: 2.0 * g * x + v * v)';
}
