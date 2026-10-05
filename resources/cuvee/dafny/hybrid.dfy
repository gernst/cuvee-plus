// the definitions of parallel composition, which are injected after prelude.dfy with the option -hybrid:
// the events of parallel components, messages with values sent and received on channels and the passing of time,
// and histories of events, whose methods send and receive return the extended history as an additional result;
// the input declares the global variable history of an instance of this type (see examples/dafny/par.dfy)
type chan
datatype event<a₀> = message(chan: chan, value: a₀) | time(time: real)

datatype history<a₀> = history(events: seq<event<a₀>>)
{
  method send(c: chan, v: a₀) returns (h: history<a₀>)
    ensures h.events == this.events + [message(c, v)]

  method receive(c: chan) returns (v: a₀, h: history<a₀>)
    ensures h.events == this.events + [message(c, v)]
}

// the values of the messages on channel c in a sequence of events
function project<a₀>(c: chan, h: seq<event<a₀>>): seq<a₀>

axiom <a₀> forall c: chan ::
  project(c, [] as seq<event<a₀>>) == []

axiom <a₀> forall c: chan, e: event<a₀> ::
  project(c, [e]) == (if e.message? && e.chan == c then [e.value] else [])

axiom <a₀> forall c: chan, h₁: seq<event<a₀>>, h₂: seq<event<a₀>> ::
  project(c, h₁ + h₂) == project(c, h₁) + project(c, h₂)
