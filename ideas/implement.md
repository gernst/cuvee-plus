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

Not supported by decision: implementing methods, patterns other than a function applied to a permutation of the
inputs, receivers whose representation changes, rewriting the bodies of implementations.
