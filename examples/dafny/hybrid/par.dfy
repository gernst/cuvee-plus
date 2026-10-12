// ./Cuvee.sh -hybrid -vcgen -simplify examples/dafny/hybrid/par.dfy
// methods with assumption-commitment contracts over the global history of events,
// composed in parallel, verified with -hybrid -vcgen,
// where -hybrid declares the type of histories with the methods send and receive,
// which return the extended history (see resources/cuvee/dafny/hybrid.dfy)

// the global history, whose events carry values of type int
var history: history<int>

// all values on channel c are positive
predicate positive(h: seq<event<int>>, c: chan)
{
  forall e: event<int> :: e in h && e.message? && e.chan == c ==> 0 < e.value
}

// sends positive values on c
method producer(c: chan, n: int)
  modifies history
  requires 0 < n
  assumes positive(history.events, c)
  commits positive(history.events, c)
{
  history := history.send(c, n);
  history := history.send(c, n + 1);
}

// receives on d, which keeps the values on c positive
method consumer(c: chan, d: chan) returns (x: int)
  modifies history
  requires c != d
  assumes positive(history.events, c)
  commits positive(history.events, c)
{
  x, history := history.receive(d);
}

method main(c: chan, d: chan, n: int) returns (x: int)
  modifies history
  requires c != d && 0 < n && positive(history.events, c)
  ensures positive(history.events, c)
{
  parallel {
    producer(c, n);
    x := consumer(c, d);
  }
}
