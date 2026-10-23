# Nondeterminism: determinization by an oracle (proposal, not implemented)

Make every program a deterministic function of its inputs and an **oracle**, a sequence of nondeterministic values
that all sources of nondeterminism read from. Verification results do not change, since the oracle is arbitrary;
what changes is that each choice becomes a term that can be named, related across iterations, and reported.

## Uses

- **Violation witnesses:** a refutation's model gives the oracle, i.e., the nondeterministic values of the violating
  run in order, which the witnesses of SV-COMP need ([witnesses.md](witnesses.md)).
- **`-teq`:** the choices of a loop become reads of the oracle at positions linear in the iteration counter, like the
  reads of an array, instead of fresh variables per path that the engine generalizes over.
- **Implementations:** a nondeterministic implementation can stay an expression, `f(args, nondet(k))`, instead of a
  call (the variant dropped in [implement.md](implement.md)).
- Simulation and tests: a run is replayed from the oracle.

## The oracle

- `function nondet<a>(k: int): a`, uninterpreted and without axioms, hence consistent with anything, and a global
  counter `var ticks: int` that only increases; a choice reads `nondet(ticks)` and increments `ticks`. Within one
  statement the reads are numbered in the order of evaluation (`ticks + i`, then `ticks := ticks + n`), so the values
  of distinct choices of a run are independent.
- Both are declared by an entry module injected with the option, as `teq.dfy` and `implement.dfy` are.
- Procedures that choose, directly or by calls, get `ticks` in their `:modifies` and `ensures old(ticks) <= ticks`, so
  that a callee never reuses its caller's values; recursion is fine.

## The sources and their translation

| Source | Core | Determinized |
|---|---|---|
| havoc, `x := *`, SV-LIB `havoc`, C `__VERIFIER_nondet_*` (within the range of the type) | `Spec(xs, true, φ)` | `xs := nondet(ticks + i)`, `ticks += n`, `assume φ` |
| specification statements | `Spec(xs, pre, φ)` | `assert pre` first, then as above |
| uninitialized locals and outputs | `Block(locals, …)`, outputs of a procedure | initialized from the oracle at the beginning of the block or body |
| nondeterministic choice, `if *` | `Choice(p₁, …, pₙ)` | `c := nondet<int>(ticks)`, `ticks++`, branch `pᵢ` on `c mod n == i` (binary: `nondet<bool>`) |
| nondeterministic iteration, `while *` | `Iter(body)` | `while nondet<bool>(ticks) { ticks++; body }`: one read per decision to continue |
| calls by a contract, implementations by methods | `Call` of a procedure with a contract | the results and modified globals from the oracle, then `assume` the postcondition (`old` the values before) |
| differential equations | `Ode` | the duration and the final values from the oracle, then `assume` the evolution constraint and invariants |
| parallel composition | `Par` (histories) | out of scope: the interleavings are abstracted by assumption-commitment contracts, whose histories would be read from the oracle in the same way |

Assumptions remain: they exclude oracles, as they exclude runs. Inputs and the initial values of global variables are
parameters, not choices; underspecified functions (`map.get` outside the keys) are deterministic and stay.

## Where and how

- A transform `-determinize`, after `-implement` and before `-vcgen`, `-teq`, `-chc`; it removes `Choice` and `Iter`
  and havocs, the result has `nondet` in place of fresh choices.
- Soundness: the runs of the original are the pairs of an oracle and the run of the determinized program on it; the
  oracle is universally quantified (uninterpreted), so a goal holds for one iff it holds for the other.
- `-chc` needs care: Horn clauses do not admit uninterpreted functions in the clauses, so `nondet` would become an
  array threaded through the predicates, or `-chc` keeps the nondeterministic form.

## Alternatives

- **Fresh variables per occurrence** (the current form): no counter, but nothing to name across iterations or report.
- **An oracle parameter per procedure** (prophecy): `o: int -> a` passed to callees shifted by the caller's position;
  modular, no global `ticks`, but every signature changes.
- **Paths as positions** (the tree of choices): exact, but positions are lists, not integers.

The global counter is the simplest; the oracle parameter is the cleaner choice if `:modifies` and the monotonicity of
`ticks` become a burden.

## Open

- One counter for all types (as above) or one per type.
- Whether witnesses need the order of reads across procedures, which the global counter gives directly.
- The interaction with `Par` beyond histories.
