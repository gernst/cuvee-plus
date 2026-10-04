// methods with assumption-commitment contracts over the global history of events,
// composed in parallel, verified with -verify -z3

var history: seq<event<int>>;

method send(c: chan, v: int)
  modifies history
  ensures history == old(history) + [event(c, v)]

method receive(c: chan) returns (v: int)
  modifies history
  ensures history == old(history) + [event(c, v)]

// all values on channel c are positive, specified inductively over the history,
// which the solvers handle better than a quantifier over the indices
predicate positive(h: seq<event<int>>, c: chan)

axiom forall c: chan :: positive([], c)

axiom forall h: seq<event<int>>, c: chan, e: event<int> ::
  positive(h + [e], c) <==> positive(h, c) && (event_chan(e) == c ==> 0 < event_value(e))

// sends positive values on c
method producer(c: chan, n: int)
  modifies history
  requires 0 < n
  assumes positive(history, c)
  commits positive(history, c)
{
  send(c, n);
  send(c, n + 1);
}

// receives on d, which keeps the values on c positive
method consumer(c: chan, d: chan) returns (x: int)
  modifies history
  requires c != d
  assumes positive(history, c)
  commits positive(history, c)
{
  x := receive(d);
}

method main(c: chan, d: chan, n: int) returns (x: int)
  modifies history
  requires c != d && 0 < n && positive(history, c)
  ensures positive(history, c)
{
  parallel {
    producer(c, n);
    x := consumer(c, d);
  }
}
