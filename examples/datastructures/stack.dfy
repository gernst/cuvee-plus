datatype Stack<a>
  = Stack(xs: seq<a>)
{
  predicate isEmpty()
  {
    |this.xs| == 0
  }

  method Top()
    returns (x: a)
    requires !this.isEmpty()
    ensures x == this.xs[|this.xs| - 1]
  {
    x := this.xs[|this.xs| - 1];
  }

  method Push(x: a)
    returns (that: Stack<a>)
    ensures that.xs == this.xs + [x]
  {
    that := Stack(this.xs + [x]);
  }

  method Pop()
    returns (that: Stack<a>)
    requires !this.isEmpty()
    ensures that.xs == this.xs[..|this.xs| - 1]
  {
    that := Stack(this.xs[..|this.xs| - 1]);
  }
}
