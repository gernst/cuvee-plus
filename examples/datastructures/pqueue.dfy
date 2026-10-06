datatype PQueue<a>
  = PQueue(xs: seq<(a, int)>)
{
  // the weights are ascending, the front has the smallest weight
  predicate sorted()
  {
    forall i: int, j: int :: 0 <= i < j < |this.xs| ==> var p: (a, int), q: (a, int) := this.xs[i], this.xs[j]; p.1 <= q.1
  }

  predicate isEmpty()
  {
    |this.xs| == 0
  }

  method Min()
    returns (x: a, w: int)
    requires !this.isEmpty()
    ensures (x, w) == this.xs[0]
  {
    var p: (a, int) := this.xs[0];
    x := p.0;
    w := p.1;
  }

  method DeleteMin()
    returns (that: PQueue<a>)
    requires !this.isEmpty()
    ensures that.xs == this.xs[1..]
  {
    that := PQueue(this.xs[1..]);
  }

  // inserted behind all pairs of the same weight, i.e., FIFO among equal weights
  method Insert(x: a, w: int)
    returns (that: PQueue<a>)
    requires this.sorted()
    ensures that.sorted()
    ensures exists k: int :: 0 <= k <= |this.xs| && that.xs == this.xs[..k] + [(x, w)] + this.xs[k..]
  {
    var k: int := 0;
    while k < |this.xs| && var p: (a, int) := this.xs[k]; p.1 <= w
      invariant 0 <= k <= |this.xs|
      invariant forall i: int :: 0 <= i < k ==> var p: (a, int) := this.xs[i]; p.1 <= w
    {
      k := k + 1;
    }
    that := PQueue(this.xs[..k] + [(x, w)] + this.xs[k..]);
  }
}
