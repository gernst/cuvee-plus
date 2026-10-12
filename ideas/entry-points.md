# Entry points

Proposal of Oct 12, 2026, implemented the same day (see Implementation at the end). Where executions start decides
which procedures are checked for all inputs of their precondition and which only in the context of their calls.
Before, each transform had its own notion, none came from the input.

## Problem

Under `-teq -fallback -z3 -verify`, `sv-benchmarks/c/array-examples/sanfoundry_24-1` and `verifythis/lcp` (both
expected true) are answered `incorrect`: TEQ emits a goal for every procedure, also for `printEven(int i)`, which
asserts `i % 2 == 0` and which `main` calls only with even numbers, and for `check(a, n, x, y, l)` of `lcp`, which
holds only for the `l` that `main` computes. Without a contract, the precondition of these goals is `true`, z3
refutes them (`i = 1`), and `-verify` takes the refutation for a counterexample. Without z3 the goals stay open
(`unknown`), but a refutation by the simplifier (`goal false`) would be wrong the same way. The goal of `main`
inlines both calls (`TEQ.call`) and checks their assertions in context already; the goals of the callees are
redundant and too strong.

| Transform | Entry points today | Calls of other procedures |
|---|---|---|
| `VCGen` (`-vcgen`) | every procedure, against its contract | by the contract of the callee (`VCGen.instance`) |
| `TEQ` (`-teq`) | every procedure, with its contract, `true` without | inlined, procedures with a contract not supported (`TEQ.call`) |
| `Horn` (`-chc`) | the procedures that no procedure calls (`Horn.called`), and the `verify-call` commands of SV-LIB | the precondition predicate of the callee is a goal at the call, inferred |

`VCGen` is modular by design: every procedure is verified against its contract, also an empty one. It stays as it
is; for the ACSL tasks, a function whose proof needs a context needs a precondition (none of the 838 tasks lacks
one where it matters: only `loops/lu.cmp` has functions without a contract, which assert nothing).

## Design

- **`entry: Option[Name]` in the state** (`core.State`), the procedure where executions start, set by the frontend,
  which knows the language: the C frontend sets `Some(main)` (SV-COMP: executions start in `main`); Dafny, Boogie,
  SMT-LIB and SV-LIB leave it `None`.
- **`-entry <name>` in the config** overrides it, e.g. to check a C program from another function, or to give the
  entry point of a Dafny or Boogie program to `-chc`. The flag sets the field of the state after the frontend
  (a stage at the beginning of the pipeline, or the source after parsing).
- **C needs an entry point**: a C program without `main` and without `-entry` is an error for the transforms that
  read it (`-teq`, `-chc`), which rules out a vacuous `correct`; parsing and printing are not affected.
- **`Some(p)` with `p` not defined is an error**, `(error "entry point not defined" p)`, at the first transform
  that reads it.
- **Which procedures are checked is up to the technique, not the language**: `VCGen` checks all of them against
  their contracts and ignores the entry point; `Horn` gives the procedures other than the entry point trivial
  contracts implicitly, their preconditions inferred from their calls; `TEQ` inlines calls anyway and needs a goal
  for the entry point only. Whether the unreached procedures should be checked is therefore moot.
- No attribute on procedures, no default that guesses: a single optional entry point covers C and SV-COMP; SV-LIB
  has its own entry points, the `verify-call` commands; several entry points could replace the `Option` by a set
  later without changing the transforms much.

## The transforms

| | `Some(p)` | `None` |
|---|---|---|
| `TEQ` | a goal only for `p`; the other procedures are inlined at their calls, their assertions checked in context; a procedure that nothing reaches from `p` is not checked | a goal for every procedure, as now |
| `Horn` | the entry clause from the precondition only for `p`; the preconditions of all other procedures are inferred from their calls | an error, `(error "-chc needs an entry point" ...)`, unless the input has `verify-call` commands (SV-LIB), which are the entry points as now |
| `VCGen` | ignores the entry point: every procedure against its contract | unchanged |

- **Horn requires an entry point.** `Horn.called` (uncalled procedures are entries) goes away: in C, a helper that
  nothing calls is not verified at all (it was an entry before, verified for arbitrary arguments, which could give
  wrong `false` answers); in SV-LIB the `verify-call` commands are the entries; Dafny, Boogie, SMT-LIB with
  procedures need `-entry` (an error without).
- **TEQ with `Some(p)`** emits the goal of `p` only. The goals of the other procedures are dropped, not marked
  `:abstract`: their assertions are checked inlined at every call that `p` reaches. Calls of procedures with a
  contract stay unsupported in TEQ (an error, as now). Procedures that `p` does not reach are not checked, as in
  SV-COMP; with `-verify` the answer covers the executions from `p`.
- **`-verify`** needs no change: the goals of TEQ and the clauses of Horn are about the executions from the entry
  point; `VCGen` stays faithful to the contracts.

## Changes

1. `core/State.scala`: the field `entry: Option[Name] = None`, kept by `copy`, a method to set it.
2. `c/Parser.scala` (`resolve`): `state = state.copy(entry = Some("main"))` always, unless `-entry` gives another
   one; `-teq` and `-chc` on C without `main` then report `(error "entry point not defined" "main")`.
3. `Config.scala`: the flag `-entry <name>`, the field `entry: Option[String]`, applied after the frontend.
4. `verify/TEQ.scala` (`verify`, `DefineProc`): with `Some(p)`, emit the goal only for `name == p`.
5. `verify/Horn.scala` (`horn`, `DefineProc`, the line `if called(state, name)`): with `Some(p)`, the entry clause
   for `p` only; with `None` and no `verify-call`, the error; `called` removed.
6. Docs: `doc/architecture.md` (the stages and transforms), `doc/teq.md` (procedures), `CLAUDE.md` (SV-LIB entry
   points), `README.md` (the options), `ideas/verify-answers.md` (the refutations of out-of-context goals).

## Affected examples

To be adapted with the implementation (the flag does not exist yet):

- `-chc` without `verify-call` and outside C get `-entry <name>` in their command lines, the procedure that is not
  called in each (the current rule), and their expected outputs regenerated:
  `examples/dafny/horn/{max, invalid_max, contract, invalid_contract, sorts, loop}.dfy`,
  `examples/dafny/parsing/{horn_entry, horn_contract}.dfy` (`horn_entry` documents the current rule: "the entry
  points are the procedures that are not called, here g"), `examples/boogie/horn/{max, globals,
  invalid_globals}.bpl`; `examples/smtlib/transform/horn_logic.smt2` and `examples/smtlib/verify/check_sat.smt2`
  if they define procedures (to check).
- `-chc` on SV-LIB (`examples/svlib/horn/*`, `examples/svlib/verify/chc.svlib`): unchanged, the `verify-call`
  commands are the entries; to check that no SV-LIB procedure relied on being uncalled.
- C without `main`: `examples/c/horn/increments.c`, whose function `f` becomes `main`.
- C with several functions and `-teq`: expected outputs lose the goals of the callees; to be checked later, one by
  one, and regenerated deliberately.

## Tests

- C, a helper with an assertion that holds for its calls from `main` only: `-teq -verify` and `-chc -z3 -verify`
  answer `correct` (before: `unknown`, and `incorrect` with `-fallback -z3`); `-vcgen -z3 -verify` stays faithful
  to the empty contract (`incorrect`).
- C, a helper that nothing calls, whose assertion fails: `correct` under `-teq` and `-chc`.
- C without `main` and without `-entry`: the error under `-teq` and `-chc`; with `-entry f`: as for `main`.
- `-entry` on a Dafny and a Boogie program with `-chc`.
- Dafny/Boogie `-chc` without `-entry`: the error; SV-LIB `-chc`: unchanged; `-vcgen` with and without `-entry`:
  the same goals.
- Regressions: `sanfoundry_24-1`, `lcp` (`-teq -fallback -z3 -verify` no longer `incorrect`).

## Decided

- C without `main` and without `-entry`: an error (strict).
- `VCGen` ignores the entry point.
- Which procedures are checked follows from the technique (see Design); no further rule.

## Implementation

As designed, except that the entry point is in the configuration, not the state: a stage builds its state from the
commands it receives (`State.add`), so a field that the C parser sets would not reach the transforms.

- `Config.entry` (`-entry <name>`) and `Config.entryPoint`: the flag, otherwise `main` if the program is C
  (`Config.program`, which resolves a task definition to the language of its input file).
- `TEQ`: a goal for the entry point only; at the end of the input, `(error "entry point not defined" ...)`.
- `Horn`: the entry clause for the entry point only, `Horn.called` removed; without an entry point outside SV-LIB,
  `(error "-chc needs an entry point, e.g. -entry <name>" ...)`.
- Examples: `-entry` in the Dafny and Boogie examples of `-chc` (the procedure that is not called) and in the 34
  `-teq` examples with a clear entry point (a single method, and `g` of `teq_no_body`; the outputs are unchanged);
  `c/horn/increments.c` with `main`; `svlib/vcgen/invalid_tagged_sequence.svlib` calls `main` with `l > n`, which
  violates the location invariant also from the verify-call (with `(1 5)` it holds there, and `-chc` answered
  `correct`); new tests `c/verify/entry_context.c` (and `_vcgen`), `entry_unreached.c`, `entry_flag.c`,
  `invalid_no_entry.c`, `dafny/parsing/invalid_horn_no_entry.dfy`; the unit tests of `-chc` on Dafny and Boogie
  with `-entry main`.
