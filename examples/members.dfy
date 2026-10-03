// member access on results of polymorphic functions, whose type is only known after type checking
datatype pair<a> = pair(fst: a, snd: a)
{
  predicate same() { this.fst == this.snd }
}

function id<b>(x: b): b

predicate both(p: pair<int>) { id(p).same() && id(p).fst == p.snd }
