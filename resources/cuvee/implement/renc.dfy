// maps implemented by the heap encoding Enc_R (Esen, Rümmer, Weber, "Sound and Complete Invariant-Based Heap
// Encodings", arXiv 2504.15844), -include implement:renc: the map is gone, the keys play the addresses and the values
// the objects; every observation of a map, a read m[k] or a test k in m, is numbered by cnt and takes its answer from
// an uninterpreted predicate, except those of the prophecy key of the map, which take the true answer and assert the
// predicate for it; a Horn solver infers the predicates (-chc), which are thereby the contents of the maps. The
// methods are meant to be inlined into the program (-instrument), as the paper's encoding is a program transformation;
// as calls, -chc would summarize the generic methods by polymorphic clauses.
//
// Limits: the inputs `in` of the paper's R(in, cnt, obj) are omitted, since a module does not know the inputs of the
// program: the encoding stays sound, but is complete only for programs whose observations do not depend on their
// inputs. The paper also requires deterministic programs (nondeterminism as inputs, see ideas/nondet.md); otherwise
// the predicates need not be functions, which again keeps soundness and may lose completeness. The predicates are
// polymorphic in the type of the values, one per instance for a solver. Dafny itself reserves `map`, Cuvée's dialect
// does not.

// the value of the read numbered c
predicate {:implement} R<b>(c: int, v: b)

// the answer of the test k in m numbered c: not in the paper, whose heaps have no membership test (the validity of an
// address follows from the allocation counter); a test observes the map like a read, hence it needs a predicate of its
// own, or both could be one predicate over the pair of answer and value
predicate {:implement} K(c: int, d: bool)

// the number of the last observation, the only global state: a read would otherwise change its receiver (methods have
// a single output, values are immutable); it only increases, never reset, so the observations of all maps are
// numbered apart and R and K stay functions of the number
var {:implement} cnt: int

// each map value carries the state of the encoding for its own prophecy: the key last_key, chosen when the map is
// created, the value last stored there, and whether one was; hence the encoding is generic in the types of keys and
// values (a global prophecy would fix the type of the keys), stores are functions of the map, and several maps have
// prophecies of their own (the paper's single global heap has one); last_def replaces the paper's bound of the
// allocated addresses, since maps have no allocation
datatype {:implement} map<a, b> = map_(last_key: a, last: b, last_def: bool)
{
  // a read: the true value at the prophecy key, an arbitrary value of R elsewhere
  method {:implement this[k]} get(k: a) returns (v: b)
    modifies cnt
  {
    cnt := cnt + 1;
    if last_key == k && last_def {
      assert R(cnt, last);
      v := last;
    } else {
      v := *;
      assume R(cnt, v);
    }
  }

  // a store changes the state of the encoding only at the prophecy key; it observes nothing, hence it is a function,
  // not a method
  function {:implement this[k := v]} put(k: a, v: b): map<a, b>
  {
    if last_key == k then map_(k, v, true) else this
  }

  // a test: the true answer at the prophecy key, an arbitrary answer of K elsewhere
  method {:implement k in this} has(k: a) returns (d: bool)
    modifies cnt
  {
    cnt := cnt + 1;
    if last_key == k {
      assert K(cnt, last_def);
      d := last_def;
    } else {
      d := *;
      assume K(cnt, d);
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
