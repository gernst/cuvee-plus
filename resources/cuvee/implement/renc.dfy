// maps implemented by the heap encoding Enc_R (Esen, Rümmer, Weber, "Sound and Complete Invariant-Based Heap
// Encodings", arXiv 2504.15844), -include implement:renc: the map is gone, the keys play the addresses and the values
// the objects; every observation of a map, a read m[k] or a test k in m, is numbered by cnt and takes its answer from
// an uninterpreted predicate, except those of the prophecy key of the map, which take the true answer and assert the
// predicate for it; a Horn solver infers the predicates (-chc), which are thereby the contents of the maps. The
// methods are meant to be inlined into the program (-instrument), as the paper's encoding is a program transformation;
// as calls, -chc would summarize the generic methods by polymorphic clauses.
//
// Soundness: R is one relation for all choices of the prophecy, which forces the solver to generalize: the run whose
// prophecy is the key of a read asserts its true value, hence R admits it in every other run, which therefore can
// follow each real execution. The arguments of R may tell executions apart, never runs of one execution with
// different prophecies; hence R and K are static members of map, without the receiver, which carries the prophecy:
// as R(this, c, v), R(s, c, v) := v == s.last satisfies every assertion and lets reads at other keys see the value
// of the prophecy key (for 10 at key 1, 20 at key 2, and reads x of 1 and y of 2, z3 proves the false x == y).
// Likewise, every observation must have a run that asserts its answer, also a read of a key that is not in the map
// (arbitrary), and the numbering by cnt must not depend on the prophecy, e.g. the observations of a merge; otherwise
// the solver can block all runs at an observation and proves anything after it.
//
// Operations: reads m[k], tests k in m, stores m[k := v], removals m - s, merges m + n (also displays
// map[k := v, ...]), and the keys m.Keys are exact; |m|, m.Values, and m <= n depend on all keys and are only
// constrained at the prophecy key, sound but weak. Sets are encoded alike (set, with the predicate S): tests,
// unions, intersections, differences, and displays are exact, |s|, s <= t, and s < t weak. The two meet at their
// representations only: the bodies of implementations are not rewritten, hence the operations of maps on sets read
// the fields of the set and assert or assume set.S themselves, and never apply an implemented function (which would
// stay an uninterpreted function on representations).
//
// Context: the paper's R(in, cnt, obj) has the inputs of the program, which the module does not know; instead, get
// and has receive the context of the client by {:context ctx}, which -implement and -instrument fill with the
// variables in scope at the read, except those that carry the prophecy (variables of map, cnt), see
// Implement.context; R and K are polymorphic in its type, a tuple that -monomorph instantiates and -flat flattens
// (in this order). Without it, a read sees the values of all inputs (m[1] after m[1 := a] is any value).
//
// Limits: whatever R cannot tell apart is merged, which keeps soundness and loses completeness:
// - cnt starts with an arbitrary value, hence each read has every number and sees the values of all reads (two reads
//   of 10 and 20 may each see both); the program can reset cnt := 0 at the entry (modifies cnt), the module cannot;
// - the paper also requires deterministic programs (nondeterminism as inputs, see ideas/nondet.md); otherwise the
//   predicates need not be functions.
// See ideas/implement.md.
//
// The predicates are polymorphic in the types of the values and of the context, one per instance for a solver. Dafny
// itself reserves `map`, Cuvée's dialect does not.

// the number of the last observation, the only global state: a read would otherwise change its receiver (methods have
// a single output, values are immutable); it only increases, never reset, so the observations of all maps are
// numbered apart and R and K stay functions of the number, relative to its start, which is arbitrary (see Limits)
var {:implement} cnt: int

// sets by the same encoding: each set carries a prophecy element last_key and whether it is in the set, tests are
// observations numbered by cnt like those of maps, with the predicate S of their answers
datatype {:implement} set<a> = set_(last_key: a, last_def: bool)
{
  // the answer of the test numbered c in the context ctx of the client, static like R and K
  static predicate {:implement} S<x>(ctx: x, c: int, d: bool)

  // a test: the true answer at the prophecy element, an arbitrary answer of S elsewhere
  method {:implement k in this} {:context ctx} has<x>(k: a, ctx: x) returns (d: bool)
    modifies cnt
  {
    cnt := cnt + 1;
    if last_key == k {
      assert S(ctx, cnt, last_def);
      d := last_def;
    } else {
      d := *;
      assume S(ctx, cnt, d);
    }
  }

  // union, intersection, and difference keep the prophecy element of this and observe t there, once, with the
  // element in the context, as the merge of maps (see there)
  method {:implement this + t} {:context ctx} union<x>(t: set<a>, ctx: x) returns (r: set<a>)
    modifies cnt
  {
    var d: bool;
    cnt := cnt + 1;
    if t.last_key == last_key {
      assert S((ctx, last_key), cnt, t.last_def);
      d := t.last_def;
    } else {
      d := *;
      assume S((ctx, last_key), cnt, d);
    }
    r := set_(last_key, last_def || d);
  }

  method {:implement this * t} {:context ctx} inter<x>(t: set<a>, ctx: x) returns (r: set<a>)
    modifies cnt
  {
    var d: bool;
    cnt := cnt + 1;
    if t.last_key == last_key {
      assert S((ctx, last_key), cnt, t.last_def);
      d := t.last_def;
    } else {
      d := *;
      assume S((ctx, last_key), cnt, d);
    }
    r := set_(last_key, last_def && d);
  }

  method {:implement this - t} {:context ctx} minus<x>(t: set<a>, ctx: x) returns (r: set<a>)
    modifies cnt
  {
    var d: bool;
    cnt := cnt + 1;
    if t.last_key == last_key {
      assert S((ctx, last_key), cnt, t.last_def);
      d := t.last_def;
    } else {
      d := *;
      assume S((ctx, last_key), cnt, d);
    }
    r := set_(last_key, last_def && !d);
  }

  // the size and the subset relations depend on all elements, constrained at the prophecy element only (see maps)
  method {:implement |this|} size() returns (z: int)
  {
    z := *;
    assume 0 <= z && (last_def ==> 1 <= z);
  }

  method {:implement this <= t} subset(t: set<a>) returns (d: bool)
  {
    if last_def && t.last_key == last_key && !t.last_def {
      d := false;
    } else {
      d := *;
    }
  }

  method {:implement this < t} proper(t: set<a>) returns (d: bool)
  {
    if last_def && t.last_key == last_key && !t.last_def {
      d := false;
    } else {
      d := *;
    }
  }
}

// each map value carries the state of the encoding for its own prophecy: the key last_key, chosen when the map is
// created, the value last stored there, and whether one was; hence the encoding is generic in the types of keys and
// values (a global prophecy would fix the type of the keys), stores are functions of the map, and several maps have
// prophecies of their own (the paper's single global heap has one); last_def replaces the paper's bound of the
// allocated addresses, since maps have no allocation
datatype {:implement} map<a, b> = map_(last_key: a, last: b, last_def: bool)
{
  // the value of the read numbered c in the context ctx of the client, the variables in scope where the read happens,
  // which tell executions apart, e.g. the paper's inputs (see Implement.context); static, since this carries the
  // prophecy (see Soundness), hence R<b, x> of the values and the context only
  static predicate {:implement} R<x>(ctx: x, c: int, v: b)

  // the answer of the test k in m numbered c: not in the paper, whose heaps have no membership test (the validity of
  // an address follows from the allocation counter); a test observes the map like a read, hence it needs a predicate
  // of its own, or both could be one predicate over the pair of answer and value
  static predicate {:implement} K<x>(ctx: x, c: int, d: bool)

  // a read: the true value at the prophecy key, an arbitrary value of R elsewhere; the value of a key that is not in
  // the map is unspecified, hence arbitrary, but asserted as well: otherwise no run would assert R for the read, the
  // solver could choose it empty and block all runs there, which proves anything after the read
  method {:implement this[k]} {:context ctx} get<x>(k: a, ctx: x) returns (v: b)
    modifies cnt
  {
    cnt := cnt + 1;
    if last_key == k {
      if last_def {
        v := last;
      } else {
        v := *;
      }
      assert R(ctx, cnt, v);
    } else {
      v := *;
      assume R(ctx, cnt, v);
    }
  }

  // a store changes the state of the encoding only at the prophecy key; it observes nothing, hence it is a function,
  // not a method
  function {:implement this[k := v]} put(k: a, v: b): map<a, b>
  {
    if last_key == k then map_(k, v, true) else this
  }

  // a test: the true answer at the prophecy key, an arbitrary answer of K elsewhere
  method {:implement k in this} {:context ctx} has<x>(k: a, ctx: x) returns (d: bool)
    modifies cnt
  {
    cnt := cnt + 1;
    if last_key == k {
      assert K(ctx, cnt, last_def);
      d := last_def;
    } else {
      d := *;
      assume K(ctx, cnt, d);
    }
  }

  // the removal of the keys of s keeps the prophecy key, at which it observes s, once, with the key in the context,
  // as the merge (see there)
  method {:implement this - s} {:context ctx} remove<x>(s: set<a>, ctx: x) returns (r: map<a, b>)
    modifies cnt
  {
    var d: bool;
    cnt := cnt + 1;
    if s.last_key == last_key {
      assert set.S((ctx, last_key), cnt, s.last_def);
      d := s.last_def;
    } else {
      d := *;
      assume set.S((ctx, last_key), cnt, d);
    }
    r := map_(last_key, last, last_def && !d);
  }

  // the merge this + n, whose keys of n win (also map displays with several keys): the result keeps the prophecy key
  // of this, at which it observes n, a test and, if the key is in n, a read; their context includes the observed key,
  // which depends on the prophecy of this, but every run that observes it has a counterpart whose prophecy of n is the
  // same key and that asserts the true answer, which keeps it sound, and without which K would merge the answers of
  // n at all keys; the read is numbered even if it does not happen, since the numbers must not depend on the
  // prophecy (whether the observed key is in n), otherwise the runs of one execution would number the later
  // observations apart, the asserting runs would miss the assuming ones, and the solver could block them all
  method {:implement this + n} {:context ctx} merge<x>(n: map<a, b>, ctx: x) returns (r: map<a, b>)
    modifies cnt
  {
    var d: bool;
    var v: b;
    cnt := cnt + 1;
    if n.last_key == last_key {
      assert K((ctx, last_key), cnt, n.last_def);
      d := n.last_def;
    } else {
      d := *;
      assume K((ctx, last_key), cnt, d);
    }
    cnt := cnt + 1;
    if d {
      if n.last_key == last_key && n.last_def {
        assert R((ctx, last_key), cnt, n.last);
        v := n.last;
      } else {
        v := *;
        assume R((ctx, last_key), cnt, v);
      }
      r := map_(last_key, v, true);
    } else {
      r := this;
    }
  }

  // the size, the keys, the values, and the submap relation depend on all keys, which a single prophecy key does not
  // see: nondeterministic, constrained at the prophecy key only, which is sound, but shows nothing about other keys
  // (as uninterpreted functions they would be unsound: maps whose contents differ but whose states of the encoding
  // agree would have the same size)
  method {:implement |this|} size() returns (z: int)
  {
    z := *;
    assume 0 <= z && (last_def ==> 1 <= z);
  }

  // the keys are exact, a set that shares the prophecy key of the map
  function {:implement this.Keys} keys(): set<a>
  {
    set_(last_key, last_def)
  }

  // the values are not: an element of a set must be its prophecy element in some run, also elements that are not
  // values, which a map does not know (all keys of a map over bool may be defined); arbitrary, constrained where the
  // prophecy elements agree
  method {:implement this.Values} values() returns (s: set<b>)
  {
    s := *;
    assume last_def && s.last_key == last ==> s.last_def;
  }

  // false if the prophecy keys agree and witness a key of this that n lacks or maps elsewhere, arbitrary otherwise
  method {:implement this <= n} submap(n: map<a, b>) returns (d: bool)
  {
    if last_def && n.last_key == last_key && (!n.last_def || n.last != last) {
      d := false;
    } else {
      d := *;
    }
  }
}

// a fresh map with an arbitrary prophecy key, top-level since it has no receiver; cnt is not reset, see above
method {:implement map[]} empty<a, b>() returns (m: map<a, b>)
{
  var k: a;
  var v: b;
  k := *;
  v := *;
  m := map_(k, v, false);
}

// the empty set {} and the singleton {k} of sets, with an arbitrary prophecy element
method {:implement {}} emptyset<a>() returns (s: set<a>)
{
  var p: a;
  p := *;
  s := set_(p, false);
}

method {:implement {k}} singleton<a>(k: a) returns (s: set<a>)
{
  var p: a;
  p := *;
  s := set_(p, p == k);
}

// the singleton map[k := v], with an arbitrary prophecy key like empty, which holds v if it is k
method {:implement map[k := v]} single<a, b>(k: a, v: b) returns (m: map<a, b>)
{
  var p: a;
  var w: b;
  p := *;
  w := *;
  if p == k {
    m := map_(k, v, true);
  } else {
    m := map_(p, w, false);
  }
}
