// maps implemented by the heap encoding Enc_R (Esen, Rümmer, Weber, "Sound and Complete Invariant-Based Heap
// Encodings", arXiv 2504.15844), -include implement:renc: the map is gone, the keys play the addresses and the values
// the objects; every observation of a map, a read m[k] or a test k in m, is numbered by tick and takes its answer from
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
// (arbitrary), and the numbering by tick must not depend on the prophecy, e.g. the observations of a merge; otherwise
// the solver can block all runs at an observation and proves anything after it.
//
// Operations: reads m[k], tests k in m, stores m[k := v] (also displays map[k := v, ...], which the frontend
// stores into the singleton of the first pair), removals m - s, merges m + n, and the keys m.Keys are exact;
// m.Values and m <= n depend on all keys and are only constrained at the prophecy key, sound but weak. Sets are
// encoded alike (set, with the predicate S): tests, updates s[k := d] (also displays, which the frontend inserts
// into the singleton of the first element), unions, intersections, and differences are exact, s <= t and s < t
// weak. The sizes |m| and |s| are a predicate N of the versions, exact through stores and updates, bounded after
// bulk operations, derived in side branches (see N), such that stores stay cheap where no size is read. The two meet
// at their representations only: the bodies of implementations are not rewritten, hence the operations of maps on
// sets read the fields of the set and assert or assume set.S themselves, and never apply an implemented function
// (which would stay an uninterpreted function on representations).
//
// Context: the paper's R(in, cnt, obj) has the inputs of the program, which the module does not know; instead, the
// observations (Get, Contains, Put, ...) receive the context of the client by {:context ctx}, which -implement and
// -instrument fill with the variables in scope at the observation, except those that carry the prophecy (variables
// of map and set, tick), see Implement.context; R, K, and S are polymorphic in its type, a tuple that -monomorph
// instantiates and -flat flattens (in this order). Without it, a read sees the values of all inputs (m[1] after
// m[1 := a] is any value).
//
// Limits: whatever R cannot tell apart is merged, which keeps soundness and loses completeness:
// - tick starts with an arbitrary value, hence each read has every number and sees the values of all reads (two reads
//   of 10 and 20 may each see both); the program can reset tick := 0 at the entry (modifies tick), the module cannot;
// - the paper also requires deterministic programs (nondeterminism as inputs, see ideas/nondet.md); otherwise the
//   predicates need not be functions;
// - sizes after loops that count new keys or elements (|m| == n after n new keys) are complete in principle, but z3
//   does not find N together with K in reasonable time; loops that overwrite are fine.
// See ideas/implement.md.
//
// The predicates are polymorphic in the types of the values and of the context, one per instance for a solver. Dafny
// itself reserves `map`, Cuvée's dialect does not.

// the number of the last observation, the only global state: a read would otherwise change its receiver (methods have
// a single output, values are immutable); it only increases, never reset, so the observations of all maps and sets
// are numbered apart and R, K, S, and N stay functions of the number, relative to its start, which is arbitrary (see
// Limits)
var {:implement} tick: int

// the size of the map or set whose last change (creation, store, update, bulk operation) is numbered c: each one
// carries that number as its version, unique across maps and sets, hence one predicate for both; the changes
// assert it in side branches that end (assume false), the bridges, which assume N of the version before and the
// answers of the observations they need, such that the paths of the program, e.g. loops, do not depend on N, K, or S
// through the sizes: only reads of sizes assume N; sound by induction over the versions, since the observations
// contain the true answers
predicate {:implement} N(c: int, z: int)

// sets by the same encoding: each set carries a prophecy element last_key, whether it is in the set, and its version
// (see N); tests are observations numbered by tick like those of maps, with the predicate S of their answers
datatype {:implement} set<a> = set_(last_key: a, last_in: bool, version: int)
{
  // the answer of the test numbered c in the context ctx of the client, static like R and K
  static predicate {:implement} S<x>(ctx: x, c: int, d: bool)

  // a test: the true answer at the prophecy element, an arbitrary answer of S elsewhere
  method {:implement k in this} {:context ctx} Contains<x>(k: a, ctx: x) returns (d: bool)
    modifies tick
  {
    tick := tick + 1;
    if last_key == k {
      assert S(ctx, tick, last_in);
      d := last_in;
    } else {
      d := *;
      assume S(ctx, tick, d);
    }
  }

  // the update this[k := d], which contains k exactly if d (an insertion if d is true, displays {a, b, ...} insert
  // into {a}), changes the membership only at the prophecy element, like a store into a map; it observes the old
  // membership of k, asserted only, which the bridge assumes for the size
  method {:implement this[k := d]} {:context ctx} Update<x>(k: a, d: bool, ctx: x) returns (r: set<a>)
    modifies tick
  {
    var b: bool;
    var e: bool;
    var z: int;
    tick := tick + 1;
    if last_key == k {
      assert S(ctx, tick, last_in);
    }
    b := *;
    if b {
      e := *;
      z := *;
      assume N(version, z) && S(ctx, tick, e);
      assert N(tick, if d && !e then z + 1 else if !d && e then z - 1 else z);
      assume false;
    }
    if last_key == k {
      r := set_(k, d, tick);
    } else {
      r := set_(last_key, last_in, tick);
    }
  }

  // union, intersection, and difference keep the prophecy element of this and observe t there, once, with the
  // element in the context, as the merge of maps (see there); their bridges choose the size within the bounds of the
  // true one, at least 1 if the prophecy element is in the result
  method {:implement this + t} {:context ctx} Union<x>(t: set<a>, ctx: x) returns (r: set<a>)
    modifies tick
  {
    var d: bool;
    var b: bool;
    var y: int;
    var z: int;
    var w: int;
    tick := tick + 1;
    if t.last_key == last_key {
      assert S((ctx, last_key), tick, t.last_in);
      d := t.last_in;
    } else {
      d := *;
      assume S((ctx, last_key), tick, d);
    }
    b := *;
    if b {
      y := *;
      z := *;
      w := *;
      assume N(version, y) && N(t.version, z) && y <= w && z <= w && w <= y + z && (last_in || d ==> 1 <= w);
      assert N(tick, w);
      assume false;
    }
    r := set_(last_key, last_in || d, tick);
  }

  method {:implement this * t} {:context ctx} Inter<x>(t: set<a>, ctx: x) returns (r: set<a>)
    modifies tick
  {
    var d: bool;
    var b: bool;
    var y: int;
    var z: int;
    var w: int;
    tick := tick + 1;
    if t.last_key == last_key {
      assert S((ctx, last_key), tick, t.last_in);
      d := t.last_in;
    } else {
      d := *;
      assume S((ctx, last_key), tick, d);
    }
    b := *;
    if b {
      y := *;
      z := *;
      w := *;
      assume N(version, y) && N(t.version, z) && 0 <= w && w <= y && w <= z && (last_in && d ==> 1 <= w);
      assert N(tick, w);
      assume false;
    }
    r := set_(last_key, last_in && d, tick);
  }

  method {:implement this - t} {:context ctx} Minus<x>(t: set<a>, ctx: x) returns (r: set<a>)
    modifies tick
  {
    var d: bool;
    var b: bool;
    var y: int;
    var z: int;
    var w: int;
    tick := tick + 1;
    if t.last_key == last_key {
      assert S((ctx, last_key), tick, t.last_in);
      d := t.last_in;
    } else {
      d := *;
      assume S((ctx, last_key), tick, d);
    }
    b := *;
    if b {
      y := *;
      z := *;
      w := *;
      assume N(version, y) && N(t.version, z) && 0 <= w && y - z <= w && w <= y && (last_in && !d ==> 1 <= w);
      assert N(tick, w);
      assume false;
    }
    r := set_(last_key, last_in && !d, tick);
  }

  // the size, read from N of the version
  method {:implement |this|} Size() returns (z: int)
  {
    z := *;
    assume N(version, z);
  }

  // the subset relations depend on all elements, constrained at the prophecy element only (see maps)
  method {:implement this <= t} Subset(t: set<a>) returns (d: bool)
  {
    if last_in && t.last_key == last_key && !t.last_in {
      d := false;
    } else {
      d := *;
    }
  }

  method {:implement this < t} Proper(t: set<a>) returns (d: bool)
  {
    if last_in && t.last_key == last_key && !t.last_in {
      d := false;
    } else {
      d := *;
    }
  }
}

// each map value carries the state of the encoding for its own prophecy: the key last_key, chosen when the map is
// created, the value last stored there, and whether one was; hence the encoding is generic in the types of keys and
// values (a global prophecy would fix the type of the keys), and several maps have prophecies of their own (the
// paper's single global heap has one); last_in replaces the paper's bound of the allocated addresses, since maps have
// no allocation; version is the version, the number of the last change, for its size (see N)
datatype {:implement} map<a, b> = map_(last_key: a, last: b, last_in: bool, version: int)
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
  method {:implement this[k]} {:context ctx} Get<x>(k: a, ctx: x) returns (v: b)
    modifies tick
  {
    tick := tick + 1;
    if last_key == k {
      if last_in {
        v := last;
      } else {
        v := *;
      }
      assert R(ctx, tick, v);
    } else {
      v := *;
      assume R(ctx, tick, v);
    }
  }

  // a store changes the value only at the prophecy key; it observes whether k is new, a test, asserted only, which
  // the bridge assumes for the size, such that the path of the program does not depend on K (stores in loops stay
  // cheap); a method, hence stores in specifications are errors with renc
  method {:implement this[k := v]} {:context ctx} Put<x>(k: a, v: b, ctx: x) returns (r: map<a, b>)
    modifies tick
  {
    var t: bool;
    var e: bool;
    var z: int;
    tick := tick + 1;
    if last_key == k {
      assert K(ctx, tick, last_in);
    }
    t := *;
    if t {
      e := *;
      z := *;
      assume N(version, z) && K(ctx, tick, e);
      assert N(tick, if e then z else z + 1);
      assume false;
    }
    if last_key == k {
      r := map_(k, v, true, tick);
    } else {
      r := map_(last_key, last, last_in, tick);
    }
  }

  // a test: the true answer at the prophecy key, an arbitrary answer of K elsewhere
  method {:implement k in this} {:context ctx} Contains<x>(k: a, ctx: x) returns (d: bool)
    modifies tick
  {
    tick := tick + 1;
    if last_key == k {
      assert K(ctx, tick, last_in);
      d := last_in;
    } else {
      d := *;
      assume K(ctx, tick, d);
    }
  }

  // the removal of the keys of s keeps the prophecy key, at which it observes s, once, with the key in the context,
  // as the merge (see there); its bridge chooses the size within the bounds of the true one
  method {:implement this - s} {:context ctx} Remove<x>(s: set<a>, ctx: x) returns (r: map<a, b>)
    modifies tick
  {
    var d: bool;
    var t: bool;
    var y: int;
    var z: int;
    var w: int;
    tick := tick + 1;
    if s.last_key == last_key {
      assert set.S((ctx, last_key), tick, s.last_in);
      d := s.last_in;
    } else {
      d := *;
      assume set.S((ctx, last_key), tick, d);
    }
    t := *;
    if t {
      y := *;
      z := *;
      w := *;
      assume N(version, y) && N(s.version, z) && 0 <= w && y - z <= w && w <= y && (last_in && !d ==> 1 <= w);
      assert N(tick, w);
      assume false;
    }
    r := map_(last_key, last, last_in && !d, tick);
  }

  // the merge this + n, whose keys of n win: the result keeps the prophecy key of this, at which it observes n, a
  // test and, if the key is in n, a read; their context includes the observed key, which depends on the prophecy of
  // this, but every run that observes it has a counterpart whose prophecy of n is the same key and that asserts the
  // true answer, which keeps it sound, and without which K would merge the answers of n at all keys; the read is
  // numbered even if it does not happen, since the numbers must not depend on the prophecy (whether the observed key
  // is in n), otherwise the runs of one execution would number the later observations apart, the asserting runs
  // would miss the assuming ones, and the solver could block them all; its bridge chooses the size within the bounds
  // of the true one
  method {:implement this + n} {:context ctx} Merge<x>(n: map<a, b>, ctx: x) returns (r: map<a, b>)
    modifies tick
  {
    var d: bool;
    var v: b;
    var t: bool;
    var y: int;
    var z: int;
    var w: int;
    tick := tick + 1;
    if n.last_key == last_key {
      assert K((ctx, last_key), tick, n.last_in);
      d := n.last_in;
    } else {
      d := *;
      assume K((ctx, last_key), tick, d);
    }
    tick := tick + 1;
    t := *;
    if t {
      y := *;
      z := *;
      w := *;
      assume N(version, y) && N(n.version, z) && y <= w && z <= w && w <= y + z && (last_in || d ==> 1 <= w);
      assert N(tick, w);
      assume false;
    }
    if d {
      if n.last_key == last_key && n.last_in {
        assert R((ctx, last_key), tick, n.last);
        v := n.last;
      } else {
        v := *;
        assume R((ctx, last_key), tick, v);
      }
      r := map_(last_key, v, true, tick);
    } else {
      r := map_(last_key, last, last_in, tick);
    }
  }

  // the size, read from N of the version
  method {:implement |this|} Size() returns (z: int)
  {
    z := *;
    assume N(version, z);
  }

  // the values and the submap relation depend on all keys, which a single prophecy key does not see:
  // nondeterministic, constrained at the prophecy key only, which is sound, but shows nothing about other keys (as
  // uninterpreted functions they would be unsound: maps whose contents differ but whose states of the encoding agree
  // would be indistinguishable)

  // the keys are exact, a set that shares the prophecy key and the version of the map, hence its size; KeySet and
  // ValueSet, not Keys and Values, which would shadow the members of Dafny in the clients (m.Values would call the
  // method)
  function {:implement this.Keys} KeySet(): set<a>
  {
    set_(last_key, last_in, version)
  }

  // the values are not: an element of a set must be its prophecy element in some run, also elements that are not
  // values, which a map does not know (all keys of a map over bool may be defined); arbitrary, constrained where the
  // prophecy elements agree, with a version of its own, whose size is at most that of the map
  method {:implement this.Values} ValueSet() returns (s: set<b>)
    modifies tick
  {
    var p: b;
    var e: bool;
    var t: bool;
    var y: int;
    var w: int;
    p := *;
    e := *;
    assume last_in && p == last ==> e;
    tick := tick + 1;
    t := *;
    if t {
      y := *;
      w := *;
      assume N(version, y) && 0 <= w && w <= y && (e ==> 1 <= w);
      assert N(tick, w);
      assume false;
    }
    s := set_(p, e, tick);
  }

  // false if the prophecy keys agree and witness a key of this that n lacks or maps elsewhere, arbitrary otherwise
  method {:implement this <= n} Submap(n: map<a, b>) returns (d: bool)
  {
    if last_in && n.last_key == last_key && (!n.last_in || n.last != last) {
      d := false;
    } else {
      d := *;
    }
  }
}

// a fresh map with an arbitrary prophecy key, top-level since it has no receiver, with a version of size 0; tick is
// not reset, see above
method {:implement map[]} empty<a, b>() returns (m: map<a, b>)
  modifies tick
{
  var k: a;
  var v: b;
  k := *;
  v := *;
  tick := tick + 1;
  assert N(tick, 0);
  m := map_(k, v, false, tick);
}

// the empty set {} and the singleton {k} of sets, with an arbitrary prophecy element and a version of size 0 or 1
method {:implement {}} emptyset<a>() returns (s: set<a>)
  modifies tick
{
  var p: a;
  p := *;
  tick := tick + 1;
  assert N(tick, 0);
  s := set_(p, false, tick);
}

method {:implement {k}} singleton<a>(k: a) returns (s: set<a>)
  modifies tick
{
  var p: a;
  p := *;
  tick := tick + 1;
  assert N(tick, 1);
  s := set_(p, p == k, tick);
}

// the singleton map[k := v], with an arbitrary prophecy key like empty, which holds v if it is k, with a version of
// size 1; displays with further pairs store them into it (Dafny frontend)
method {:implement map[k := v]} single<a, b>(k: a, v: b) returns (m: map<a, b>)
  modifies tick
{
  var p: a;
  var w: b;
  p := *;
  w := *;
  tick := tick + 1;
  assert N(tick, 1);
  if p == k {
    m := map_(k, v, true, tick);
  } else {
    m := map_(p, w, false, tick);
  }
}
