# Implementations: open points

Documented in [doc/implement.md](../doc/implement.md) (0.49.0 to 0.50.2, Oct 22-23, 2026).

- **Shared abstract functions** in `implement.dfy`, e.g. `choose<a>(s: set<a>): a` with the free lemma
  `|s| > 0 ==> choose(s) in s`, used by clients and implemented by methods of modules such as `renc`. The abstract
  function stays deterministic: a client is correct under a nondeterministic implementation only if it relies on the
  axioms alone.
- **Refinement obligations as goals:** an implementation satisfies the axioms of the abstract function; for a method,
  its postcondition implies them. Lemmas of the modules so far.
- **Nondeterministic implementations as expressions** (`f(args, nondet(k))` instead of a call), once nondeterminism is
  determinized ([nondet.md](nondet.md)).

## Enc_R ([renc.dfy](../resources/cuvee/implement/renc.dfy), `-instrument`)

Implemented and documented in the header of renc.dfy and in [doc/implement.md](../doc/implement.md) (maps and sets,
the context, sizes by `N`, the conditions of soundness). Open:

- **The start of `tick`** is arbitrary; the examples reset it by hand (`tick := 0`, `modifies tick`), otherwise each
  observation has every number and two reads of 10 and 20 may each see both. Options: initializers of global
  variables, an entry precondition from the module, `-instrument` resetting the globals of implementations at the
  entry, or a counter at the creation of each container (`born`) with the predicates over the difference.
- **Loops that count** (`|m| == n` after `n` new keys) are unknown to z3 even after 120 s: it must find `N` together
  with `K`, related to the loop by `version == tick - 1`; loops that overwrite are solved.
- **Costs:** a loop that reads back what a loop stored (`m[i] == 2 * i` for all `i < n`) is unknown after 60 s, a sum
  over such reads takes 28 s, a merge 29 s; most examples take 1-9 s.
- **Copies of the predicates per call** (`-instrument` renaming `R` per place) instead of one per context type, if z3
  benefits; sound, since the asserting and the assuming runs meet at the same observation.
- **A check of the bodies** of implementations: no function implemented by a method applied in them (it would stay
  an uninterpreted function on representations, as `last_key in s` in the first `remove`), and the conditions of
  soundness (an asserting run for every observation, a numbering independent of the prophecy) as syntactic checks;
  see also [renc-verification.md](renc-verification.md).

Decided against, with the reason:

- **Predicates as members with `this`:** `this` carries the prophecy, and `R(s, c, v) := v == s.last` satisfies every
  assertion while reads at other keys see the value of the prophecy key (z3 proved the false `m[1] == m[2]`).
- **The context in the constructor:** its type would be a type parameter of the datatype, `map<a, b, x>`, which
  changes the types of clients and differs per place of creation.
- **Exact values, submaps, and sizes kept as state:** values and submaps depend on all keys, which no run sees; a
  size kept in the representation needs an observation per store that the path assumes, which ties loop invariants
  to `K` (the fill loop went from 3 s to unknown), hence `N` in side branches; a prophecy of the size does not help,
  since no run can refute a wrong guess.
- **Displays as merges of singletons:** a display with two pairs took 60 s, as stores 2 s (Dafny frontend).

Not supported by decision: implementing methods, patterns other than a function applied to a permutation of the
inputs, receivers whose representation changes, rewriting the bodies of implementations.
