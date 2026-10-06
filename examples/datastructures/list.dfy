datatype List<a>
  = List(xs: seq<a>)
{
  predicate isEmpty()
  {
    |this.xs| == 0
  }

  method Length()
    returns (n: int)
    ensures n == |this.xs|
  {
    n := |this.xs|;
  }

  method Get(i: int)
    returns (x: a)
    requires 0 <= i < |this.xs|
    ensures x == this.xs[i]
  {
    x := this.xs[i];
  }

  method Update(i: int, x: a)
    returns (that: List<a>)
    requires 0 <= i < |this.xs|
    ensures that.xs == this.xs[i := x]
  {
    that := List(this.xs[i := x]);
  }

  method Prepend(x: a)
    returns (that: List<a>)
    ensures that.xs == [x] + this.xs
  {
    that := List([x] + this.xs);
  }

  method Append(x: a)
    returns (that: List<a>)
    ensures that.xs == this.xs + [x]
  {
    that := List(this.xs + [x]);
  }

  method Remove(i: int)
    returns (that: List<a>)
    requires 0 <= i < |this.xs|
    ensures that.xs == this.xs[..i] + this.xs[i + 1..]
  {
    that := List(this.xs[..i] + this.xs[i + 1..]);
  }
}
