type pair<a,b>
type option<a>

datatype stack<a>
  = stack(counter: int, size: int, elem: a, offset: int)
{
  predicate valid() {
    0 <= this.counter &&
    0 <= this.offset && this.offset < this.size
  }

  predicate isEmpty()
    requires this.valid()
  {
    this.counter == 0
  }

  method top()
    returns (result: a)
    requires this.valid()

  method pop()
    returns (this_: stack<a>)
    requires this.valid()
    requires !this.isEmpty()

  method push(elem: a)
    returns (this_: stack<a>)
    requires this.valid()
    ensures  this_.valid()
}

method test(s: stack<int>, t: stack<int>)
{
  var x: int;
}