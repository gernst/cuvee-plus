# Implementations: open points

Documented in [doc/implement.md](../doc/implement.md) (0.49.0 to 0.50.2, Oct 22-23, 2026).

- **Shared abstract functions** in `implement.dfy`, e.g. `choose<a>(s: set<a>): a` with the free lemma
  `|s| > 0 ==> choose(s) in s`, used by clients and implemented by methods of modules such as `listset`. The abstract
  function stays deterministic: a client is correct under a nondeterministic implementation only if it relies on the
  axioms alone.
- **Refinement obligations as goals:** an implementation satisfies the axioms of the abstract function; for a method,
  its postcondition implies them. Lemmas of the modules so far.
- **Nondeterministic implementations as expressions** (`f(args, nondet(k))` instead of a call), once nondeterminism is
  determinized ([nondet.md](nondet.md)).

## Enc_R ([renc.dfy](../resources/cuvee/implement/renc.dfy), `-instrument`)

Findings of Oct 23, 2026 (programs on `map<int, int>`, `-instrument -chc -entry main -flat -monomorph -z3`):

- **Soundness needs `R` independent of the prophecy.** `R` is one relation for all runs (choices of the prophecy),
  which forces the solver to generalize: the run whose prophecy is the key of a read asserts the true value, so every
  other run admits it and can follow each real execution. Arguments of `R` may tell executions apart, never the runs
  of one execution. As a member of `map`, `R(this, c, v)` sees the prophecy state; `R(s, c, v) := v == s.last`
  satisfies every assertion and lets reads at other keys see the value of the prophecy key: with 10 at key 1 and 20
  at key 2, z3 proves the false `m[1] == m[2]`. Hence `R` and `K` stay top-level.
- **Incomplete where `R` cannot tell executions apart** (whatever it cannot separate is merged):
  - Inputs: the paper's `R(in, cnt, obj)`. Without them, `m[1]` after `m[1 := a]` is any value: `assert m[1] == a`
    fails, with symbolic keys and concrete values it holds. Solved by the context (below): `in1`, `in2` hold.
  - The start of `tick`, arbitrary: each read has every number, so two reads of 10 and 20 may each see both
    (`m[1] + m[2] == 30` fails). With `tick := 0` at the beginning of `main` it holds. Open: initializers of global
    variables, an entry precondition from the module, or `-instrument` resetting the globals of implementations at
    the entry.
- Determinism: nondeterministic programs keep soundness, not completeness ([nondet.md](nondet.md)).
- **Two further conditions of soundness** (found with the operations of Oct 23, 2026, both gave `correct` for false
  assertions): every observation needs a run that asserts its answer, also a read of a key that is not in the map
  (the run whose prophecy is that key asserts an arbitrary value; before, it only assumed, so `R` could be empty and
  block all runs, [invalid_absent.dfy](../examples/dafny/renc/invalid_absent.dfy)), and the numbering by `tick` must not depend on the prophecy (the
  merge observed one or two times depending on whether the prophecy key of `m` is in `n`, so the runs of one
  execution numbered later reads apart, [invalid_merge.dfy](../examples/dafny/renc/invalid_merge.dfy)). An observation may depend on the prophecy
  of another map in its context (the merge observes `n` at the prophecy key of `m`), since its counterpart run with
  the same prophecy of `n` asserts it.
- **Operations on whole maps** (`|m|`, `m.Keys`, `m.Values`, `m <= n`) are not expressible by one prophecy key:
  nondeterministic, constrained there only, sound but they show nothing about other keys; as uninterpreted functions
  they would be unsound (maps with different contents but equal states of the encoding).
- **Sets by the same encoding** (`set` in renc.dfy, predicate `S`). Maps and sets meet at their representations
  only (`m - s` reads `s.last_key`, `m.Keys` is `set_(last_key, last_def)`), since the bodies of implementations
  are not rewritten: an implemented function applied in a body stays an uninterpreted function on representations,
  which is unsound (the first `remove` had `last_key in s`). Open: a check in `Implement` that the bodies of
  implementations apply no function implemented by a method. `m.Values` cannot be exact: every element must be the
  prophecy element of a set in some run, also those that are no values, which the map does not know.
- **Cost:** a display with two keys took z3 about 60 s as a merge of singletons, 2 s since the Dafny frontend stores
  the further pairs into the singleton of the first (sets: updates `s[x := true]` of the singleton); a loop reading what a loop stored (`m[i] == 2 * i` for all `i < n`) is unknown after 60 s,
  a sum over such reads takes 28 s; fills, counters, and tests in loops take 2-5 s.
- **Sizes by a predicate** (Oct 23, 2026): a size kept in the representation needs an observation per store (is
  the key new?), and assumed inside a loop, that observation ties the loop invariant to `K`: the fill loop went from
  3 s to unknown. Instead, `N(version, z)` relates the version of a map or set (the number of its last change) to
  its size; stores only assert their observation and derive `N` of the new version in a side branch that ends
  (`assume N(old) && K(...); assert N(new); assume false`), and only reads of sizes assume `N`. Loops stay as cheap
  as without sizes (fill 2 s, merge 29 s), straight-line sizes and a loop that overwrites one key are exact (2-9 s),
  but a loop that counts new keys or elements (`|m| == n` after storing `n` keys) is unknown after 30 s: z3 must
  find `N(c, z) <==> z == c - c0` together with `K(., c, e) <==> !e`, related to the loop by `version == tick - 1`.
  `-chc` ends paths at `assume false`.
- **Aggregates** (sizes, values, submaps) are exact only as state updated by pointwise operations (an observation
  per store), not after bulk operations (merges, removals of sets, unions), which change them by the size of an
  overlap; pointwise questions about the results of bulk operations stay exact. A prophecy of the size does not help:
  no run can refute a wrong guess, each knows one element.

### Proposal: predicates with a context of the client

The arguments of `R` and `K` are determined by the datatype (the value type `b`), the context that tells executions
apart comes from the client. Hence:

- **Static members with a polymorphic context:** `static predicate R<x>(ctx: x, c: int, v: b)` in `map<a, b>`, of
  the datatype (it uses `b`), but without `this`, which carries the prophecy. Static members get only the type
  parameters of the datatype that their signature mentions (here `b`), such that `-monomorph` can determine the
  instances. The context is a tuple, which `-monomorph` instantiates and `-flat` flattens, as for `map_` now; larger
  contexts nest tuples (the prelude has up to 10 components), the empty one needs a unit value.
- **The context reaches the body as an input that the pattern leaves out:** `method {:implement this[k]}
  get<x>(k: a, {:context} ctx: x) returns (v: b)`, with `R(ctx, tick, v)` in the body; the check that a pattern
  contains all inputs exempts it. `-instrument` passes the tuple of the place it inlines into. (A built-in `context`
  that `-instrument` substitutes would keep signatures, but has a free type parameter until then.)
- **What goes into the tuple:** the variables in scope at that place, minus those that carry the prophecy:
  variables of implemented sorts (`m` holds `last_key`) and the globals of the implementation (`tick`). `-instrument`
  builds it, so the soundness condition holds by construction. Sound since, by induction over the reads, every run
  can follow the real execution up to a read, where the variables of the program agree in all runs. Restricted to the
  inputs of the entry, it is the paper's `R(in, cnt, obj)`.
- **Not in the constructor:** the context of the creation of a map would be sound and, for maps created at the
  entry, exactly `in`, but its type would be a type parameter of the datatype, `map<a, b, x>`, whose sort has arity
  2 and whose clients' types must not change; maps created at different places would have different types. The
  constructor can carry what has a fixed type, e.g. `born: int`, the counter at the creation, which makes the start
  of `tick` irrelevant (`R(born, tick, v)` over the difference); the context comes in at the observation.
- **How many relations:** sound in all variants, since each read is self-contained (the asserting run and the
  assuming runs meet at the same read, the contents of the map travel in the prophecy, not in `R`), hence no
  chaining of instances is needed:
  - one shared `R` over a uniform context (the entry's inputs): fewest unknowns, the paper's form;
  - one per context type: what `-monomorph` gives for free with `R<x>`, instances of the same type are shared
    (sound, generalization);
  - one per call of `get`: `-instrument` renames `R` per place, many small unknowns, like the predicates of the
    program points of `Horn`.

  Start with one per context type; copies per call as an experiment if z3 benefits.

Done (Oct 23, 2026), Dafny only by decision: `static` in the Dafny frontend
([static.dfy](../examples/dafny/parsing/static.dfy)), `{:context ctx}` and `Implement.context` (the scope minus the
variables of implemented sorts and the globals of implementations, uninitialized variables included, which is sound
but adds noise), static `R<x>` and `K<x>` in `renc`
([inputs.dfy](../examples/dafny/renc/inputs.dfy)). The order is `-monomorph -flat`
(`-flat` first: "record instantiates a type parameter"). Open: the start of `tick` (`tick := 0` by hand in the
examples; `born` in the constructor), copies of `R` per call.

Not supported by decision: implementing methods, patterns other than a function applied to a permutation of the
inputs, receivers whose representation changes, rewriting the bodies of implementations.
