datatype Queue<a>
  = Queue(xs: seq<a>)
{
  predicate isEmpty()
  {
    |this.xs| == 0
  }

  method Front()
    returns (x: a)
    requires !this.isEmpty()
    ensures x == this.xs[0]
  {
    x := this.xs[0];
  }

  method Enqueue(x: a)
    returns (that: Queue<a>)
    ensures that.xs == this.xs + [x]
  {
    that := Queue(this.xs + [x]);
  }

  method Dequeue()
    returns (that: Queue<a>)
    requires !this.isEmpty()
    ensures that.xs == this.xs[1..]
  {
    that := Queue(this.xs[1..]);
  }
}
