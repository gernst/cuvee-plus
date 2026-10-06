datatype FSet<a>
  = FSet(s: set<a>)
{
  predicate isEmpty()
  {
    this.s == {}
  }

  predicate Contains(x: a)
  {
    x in this.s
  }

  method Insert(x: a)
    returns (that: FSet<a>)
    ensures that.s == this.s + {x}
  {
    that := FSet(this.s + {x});
  }

  method Remove(x: a)
    returns (that: FSet<a>)
    ensures that.s == this.s - {x}
  {
    that := FSet(this.s - {x});
  }
}
