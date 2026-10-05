// the definitions of parallel composition, which are injected after prelude.dfy with the option -hybrid:
// the events of parallel components, values sent and received on channels,
// and histories of events, whose methods send and receive return the extended history as an additional result;
// the input declares the global variable history of an instance of this type (see examples/dafny/par.dfy)
type chan
datatype event<a₀> = event(chan: chan, value: a₀)

datatype history<a₀> = history(events: seq<event<a₀>>)
{
  method send(c: chan, v: a₀) returns (h: history<a₀>)
    ensures h.events == this.events + [event(c, v)]

  method receive(c: chan) returns (v: a₀, h: history<a₀>)
    ensures h.events == this.events + [event(c, v)]
}
