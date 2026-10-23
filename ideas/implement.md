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
    fails, with symbolic keys and concrete values it holds. With a global `inp := a` as an argument of `R` (a copy of
    the module), both hold. Open: how a module gets the inputs, e.g. `-instrument` passing those of the entry, which
    makes `R` depend on the program, or a ghost global of the program.
  - The start of `cnt`, arbitrary: each read has every number, so two reads of 10 and 20 may each see both
    (`m[1] + m[2] == 30` fails). With `cnt := 0` at the beginning of `main` it holds. Open: initializers of global
    variables, an entry precondition from the module, or `-instrument` resetting the globals of implementations at
    the entry.
- Determinism: nondeterministic programs keep soundness, not completeness ([nondet.md](nondet.md)).

Not supported by decision: implementing methods, patterns other than a function applied to a permutation of the
inputs, receivers whose representation changes, rewriting the bodies of implementations.
