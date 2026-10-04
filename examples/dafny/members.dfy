// member access on variables, results of functions must be bound first
datatype pair<a> = pair(fst: a, snd: a)
{
  predicate same() { this.fst == this.snd }
}

function id<b>(x: b): b

predicate both(p: pair<int>) { var q: pair<int> := id(p); q.same() && q.fst == p.snd }
