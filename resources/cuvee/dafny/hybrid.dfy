// the definitions of parallel composition, which are injected after prelude.dfy with the option -hybrid:
// the events of parallel components, messages with values sent and received on channels and the passing of time,
// and histories of events, whose methods send, receive, and tick return the extended history as an additional result;
// the input declares the global variable history of an instance of this type (see examples/hybrid/par.dfy)
type {:hybrid} chan
datatype {:hybrid} event<a₀> = message(chan: chan, value: a₀) | time(time: real)

// the values of the messages on channel c in a sequence of events
function {:hybrid} project<a₀>(c: chan, h: seq<event<a₀>>): seq<a₀>

axiom <a₀> {:hybrid} forall c: chan ::
  project(c, [] as seq<event<a₀>>) == []

axiom <a₀> {:hybrid} forall c: chan, e: event<a₀> ::
  project(c, [e]) == (if e.message? && e.chan == c then [e.value] else [])

axiom <a₀> {:hybrid} forall c: chan, h₁: seq<event<a₀>>, h₂: seq<event<a₀>> ::
  project(c, h₁ + h₂) == project(c, h₁) + project(c, h₂)

// the passing of t time units after h, merged with the last event if that is time already
function {:hybrid} delay<a₀>(h: seq<event<a₀>>, t: real): seq<event<a₀>>

axiom <a₀> {:rw} {:hybrid} forall t: real ::
  delay([] as seq<event<a₀>>, t) == (if t == 0.0 then [] else [time(t)])

axiom <a₀> {:rw} {:hybrid} forall h: seq<event<a₀>>, c: chan, v: a₀, t: real ::
  delay(h + [message(c, v)], t) == h + [message(c, v)] + (if t == 0.0 then [] else [time(t)])

axiom <a₀> {:rw} {:hybrid} forall h: seq<event<a₀>>, s: real, t: real ::
  delay(h + [time(s)], t) == h + [time(s + t)]

datatype {:hybrid} history<a₀> = history(events: seq<event<a₀>>)
{
  method {:hybrid} send(c: chan, v: a₀) returns (h: history<a₀>)
    ensures h.events == this.events + [message(c, v)]

  method {:hybrid} receive(c: chan) returns (v: a₀, h: history<a₀>)
    ensures h.events == this.events + [message(c, v)]

  method {:hybrid} tick(t: real) returns (h: history<a₀>)
    requires 0.0 <= t
    ensures h.events == delay(this.events, t)
}
