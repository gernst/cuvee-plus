datatype MSet<a>
  = MSet(m: multiset<a>)
{
  predicate isEmpty()
  {
    this.m == multiset{}
  }

  predicate Contains(x: a)
  {
    x in this.m
  }

  method Count(x: a)
    returns (n: int)
    ensures n == this.m[x]
  {
    n := this.m[x];
  }

  method Insert(x: a)
    returns (that: MSet<a>)
    ensures that.m == this.m + multiset{x}
  {
    that := MSet(this.m + multiset{x});
  }

  // removes one occurrence of x, if any
  method Remove(x: a)
    returns (that: MSet<a>)
    ensures that.m == this.m - multiset{x}
  {
    that := MSet(this.m - multiset{x});
  }
}
