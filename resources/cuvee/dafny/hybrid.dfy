// the definitions of parallel composition, which are injected after prelude.dfy with the option -hybrid:
// the events of parallel components, values sent and received on channels,
// the global history of events, and the methods send and receive, which extend it (see examples/dafny/par.dfy)
type chan
datatype event<a₀> = event(chan: chan, value: a₀)

var history: seq<event<int>>;

method send(c: chan, v: int)
  modifies history
  ensures history == old(history) + [event(c, v)]

method receive(c: chan) returns (v: int)
  modifies history
  ensures history == old(history) + [event(c, v)]
