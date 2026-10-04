// hybrid programs: nondeterministic iterations, differential equations with evolution constraints and
// differential invariants, and derivatives (e)' with respect to the variables of e

// a bouncing ball at height x with velocity v under gravity g
method ball(g: int, h: int) returns (x: int, v: int)
  requires 0 < g && 0 <= h
{
  x, v := h, 0;
  while *
    invariant 0 <= x
  {
    x', v' == v, -g && 0 <= x
      invariant 2 * g * x + v * v <= 2 * g * h;
    if x == 0 {
      v := -v;
    }
  }
}

// the derivative of the energy, which vanishes along the trajectories of the ball
method energy(g: int, h: int) returns (e: int)
{
  var x: int, v: int;
  x, v := h, 0;
  x', v' == v, -g;
  e := (2 * g * x + v * v)';
}
