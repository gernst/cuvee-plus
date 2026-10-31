# Verification witnesses for SV-COMP

SV-COMP scores a correct verdict without a confirmed witness with 0, but a wrong one with −32 (true) or −16 (false).
Implemented (Oct 14-15, 2026): trivial witnesses of format 2.0 for C, `-witness <file>`
([doc/options.md](../doc/options.md), `yml.Witness`), and the source positions of loops and of the calls of
`reach_error`. Open: witnesses that carry invariants or the values of a violation (the plan below, from step 2), and
the witnesses of the portfolio's methods (section "After the portfolio", Oct 31).

## The formats

- **C, format 2.0/2.1** (YAML, [sv-witnesses](https://gitlab.com/sosy-lab/benchmarking/sv-witnesses), local copy
  in `~/Tools/sv-witnesses`, `user-guide/Witness-Format.md`):
  - correctness: an `invariant_set` of `loop_invariant` (evaluated before the controlling expression) and
    `location_invariant` entries, each at a file, line, column and function, whose value is a C expression
    (`c_expression`, or `ext_c_expression` with `\at(x, Pre)`); 2.1 adds ghost variables (global scalars,
    updated by C expressions at locations), function contracts and the label `inductive`. The expressions have
    **no quantifiers** and no logic functions.
  - violation: a sequence of segments of waypoints (`assumption`, `branching`, `function_enter`,
    `function_return`), the last one a `target`.
  - An empty correctness witness (`content: []`) is valid: the validator proves the task on its own. Symbiotic
    emits exactly that (`results/symbiotic.*.files/**/witness.yml`).
- **SV-LIB 1.0** (`~/Projects/sv-lib/examples/validation-with-witness`): the witness is part of the language.
  - correctness: a list of `annotate-tag` commands with `:invariant` and `:decreases`, terms of SMT-LIB in the
    logic of the task;
  - violation: `select-trace` with a model of the constants, `init-global-vars`, `entry-proc`, `steps`
    (`init-proc-vars`, and `leap <tag> (x v) ...`, which jumps to a tagged loop in a given state, without
    listing the iterations) and the `incorrect-annotation` that is violated.
  - The C-translated tasks declare `QF_LIA`, so their invariants are presumably quantifier-free; they are loops
    only, without arrays.

## The core problem: TEQ proofs contain no invariants

`-teq` summarizes a loop by trace equations, and `∃ n, K, X. TEQ` is an inductive invariant (theorem 4.7 of the
paper), but its existential ranges over sequences, not over the current state. `-prove` rewrites the goal of the
final state with the database: the result is a derivation, not an invariant. The representation gap that TEQs
avoid comes back with the witnesses.

An invariant follows from the closed forms of the traces at a generic number of iterations `n`:

- the introduction rules name the fragments (`counter`, `stores`, `consts`), the acceleration rules give their
  closed forms, `current(counter(i, c, n)) = i + n·c`, a store loop `∀ j. a[j] = (j < n ? f(j) : a0[j])`;
- `n` is eliminated by the counter, `n = (i − i0) / c`;
- the initial values `x_old` are terms over the values at the entry of the function and the nondeterministic
  values of the symbolic execution (the substitution of `TEQ.Path`); those that cannot be named any more need
  ghost variables assigned before the loop (2.1);
- the iteration constraints (`invs`) become bounds, e.g. `n <= len`.

## Challenges

1. **Quantifiers.** The strength of Cuvée is arrays: 132 to 142 safe tasks of ReachSafety-Arrays, 112 that no
   other tool of the table of [doc/paper](../doc/paper/cuvee.tex) proves. Their invariants are
   `∀ j < i. a[j] == f(j)`, which C expressions cannot state; ghost variables are scalars and cannot replace
   a quantifier. Korn instantiates at the index that the property reads (`A[N-1]`), which needs that index in
   scope at the loop and fails for check loops `for (i...) assert(a[i] == ...)`.
2. **Functions of the database** (`sum`, `count`, `max`, `pow`, `sorted`, `perm`) are recursive and cannot be
   written in C; only closed forms of arithmetic (triangle numbers) can.
3. **Partial facts are not inductive.** Forward lemmas and bounds ("max is at least every element so far") need
   not be inductive alone; a witness need not be `inductive`, but the validator then has to strengthen them.
4. **Nested loops and inlining.** An inner loop is a value of the outer update, so its invariant states the
   progress of the outer loop. `-teq` inlines calls: a loop in a function called at several sites has one
   invariant per site and one location in the witness, hence a disjunction or `\at(x, Pre)`.
5. **Source locations.** The C scanner tracks lines and columns (`%line %column` in
   [Scanner.flex](../src/cuvee/c/Scanner.flex)), the syntax and the core drop them. A witness needs the line and
   column of the loop and of the call of `reach_error()`, the names of the functions, the C names of the
   variables in scope, and the SHA-256 of the `.i` file. The evaluation point of a `for` loop (after the
   initialization and after the increment, before the test) is the head of its translation into `while`;
   `continue` remains to be checked.
6. **C semantics in the expressions.** Signed integers are mathematical integers, the ranges of nondeterministic
   values are dropped (`Config.unbounded`): an invariant such as `s <= i*255` may itself overflow in C and needs
   `(long long)` casts. `div` and `mod` of SMT-LIB round otherwise than `/` and `%` of C (a case split, or
   operands known to be nonnegative); `store` terms have no counterpart in C.
7. **Violation witnesses.** `Eval.counterexample` gives values of at most four variables of a remaining goal,
   which must be traced back to their nondeterministic calls (the numbers of iterations are dropped). All
   `__VERIFIER_assert` share one `reach_error()`, so the target needs a `function_enter` waypoint at the
   assertion, hence a map from goals (also after `-split`) to source assertions. A counterexample that depends
   on an overflow is undefined behavior, which invalidates the witness, and the verdict.
8. **The logic of SV-LIB tasks** (`QF_LIA`) presumably excludes quantified invariants.

## What the validators prove alone

Cuvée's runs of Oct 13, 2026 (`results/cuvee.2026-10-13_22-11-17`, `-21`) against the official results of
SV-COMP 2026 of CPAchecker and UAutomizer, which are also validators, as an estimate of what an empty witness
gets confirmed:

| | Cuvée correct | also confirmed by CPAchecker or UAutomizer |
|---|---|---|
| Arrays true | 138 | 5 |
| Arrays false | 9 | 0 |
| Loops true | 149 | 119 |
| Loops false | 16 | 7 |

An empty witness recovers most of Loops and almost nothing of Arrays, where the witness has to carry the proof.

## Plan, cheapest first

1. **Trivial witnesses**, done: for true an `invariant_set` without invariants, for false a `violation_sequence` with
   a single segment, the target at the call of `reach_error` or `__VERIFIER_error` (none if the program has no call
   or several, 85 of the 1430 tasks of Arrays, Loops, and VerifyThis-Loops); `-witness witness.yml` is in
   `xml/cuvee*.xml`. Open: fm-tools, and the measurement with the validators of svcomp-bench-defs
   (`validate-correctness-witnesses-2.0`, `validate-violation-witnesses-2.0`), expected about 120 confirmed results
   of Loops.
2. **Invariants of `-chc`.** The model of Z3 gives the predicates of the loop heads. In SV-LIB nearly for free:
   the model is SMT-LIB already, its arguments are renamed to the variables in scope at the tag, the values at the
   entry become `(at x tag)`, and `get-witness` prints the `annotate-tag` commands. In C the same with the
   translation of challenge 6. The derivation of `unsat` gives the nondeterministic values of a violation, as
   assumption waypoints.
3. **Invariants of TEQ for scalar loops.** The construction above for counters, polynomial closed forms
   (nla-digbench) and bounds, checked by Cuvée itself: printed as ACSL loop invariants (the C printer prints
   `\forall`) and run with `-vcgen -z3`, as for [benchmarks/acsl](../benchmarks/acsl); only invariants that
   pass are emitted, which also catches wrong verdicts. Violations in SV-LIB suit TEQ: `leap` reaches the state
   after `n` iterations without the iterations.
4. **Quantified invariants for arrays**, a question of the format first: propose a keyword `\forall` for
   `ext_c_expression` (its keywords are designed for extension) or invariants in ACSL (which Ultimate reads), to
   the community of SV-COMP, with the 112 unique proofs as the case. Meanwhile, instantiation at the indices that
   the property reads, where they are in scope.
5. **Scoring.** A true without a confirmed witness gives 0 and risks −32: in a competition configuration, answer
   true only with a witness that checks. The run of CTranslated of Oct 14, 2026 has one wrong true that this
   would have caught.

## Invariants from the TEQ system, without the goal (Oct 24, 2026)

The target is SV-LIB, whose witnesses must be strictly inductive (C needs none for Arrays, an empty one suffices
mostly for Loops). The conventions of sv-benchmarks (`sv-lib/CONVENTIONS.md`) ask for "a full correctness witness
containing the invariants and function contracts required for a modular proof": an `:invariant` at every tagged
loop, presumably contracts of the called procedures. The 253 tasks of `c-translated` declare QF_LIA (168), QF_NIA
(58: loop-acceleration, loops-crafted-1, loop-invgen, ...), QF_ALIA (20) and ALL (7); whether a witness may leave the
logic of its task (quantified invariants for QF_ALIA) is to be checked in the standard.

**Start easy** (the user's decision, Oct 24, 2026): take the invariant that the system is already, `∃ n, K, X. TEQ`
with the state as the `current` of its traces (theorem 4.7), not an invariant extracted from the proof of the goal (a
derivation, see above):

1. **Simplify it** with the simplifier and the database of `-prove`, without the goal: the rules that give closed
   forms (`current(counter(i, c, n)) = i + n·c`, the series facts) remove the traces where they can, and equations
   such as `x = x0 + n` eliminate `n`. For `loop-add` of SV-LIB's examples, `x = x0 + n`, `y = y0 - n`, `n <= y0`
   give `x + y = x0 + y0` and `0 <= y`, its witness.
2. **Lower it, potentially**, where traces remain, by the encoding of `-fallback` (traces and folds in first-order
   logic); open whether a witness may declare the functions that the lowering needs.
3. Print it as `annotate-tag :invariant` at the tag of the loop.

The invariant is inductive by the theorem, as long as simplification and lowering preserve equivalence; whether the
validator can check it is another question. Later, only if needed: candidates beyond the system (bounds, parities of
`phases_*`) made inductive by Houdini, a check of the witness by `-vcgen -z3`, the invariants of `-chc` as a second
source, nested loops and the contracts of called procedures (`-teq` inlines calls). Open: the scoring of a correct
verdict without a valid witness in SV-LIB.

Implemented as `-slice` (Oct 25, 2026, [doc/prove.md](../doc/prove.md), "Programs"): the simplifier of procedures
(`Slice`) takes the system of each loop as its head, simplified in the context before the loop, and attaches it as an
`invariant` over the program variables, the remaining choices quantified existentially, e.g. `tot == 2 * idx && idx
<= len && 0 <= idx`. Open: lowering the traces and `invs` that remain, printing the invariants as `annotate-tag`
commands of SV-LIB at the tags of the loops, and checking them (`-vcgen`).

## After the portfolio (Oct 31, 2026): who needs which witness

The portfolio (portfolio.py, doc/benchmarks.md) answers with the first method that is definite; its cloud run of
Oct 31 (0.53.26, 300 s, 4 cores) answered as follows (the correct answers, by the method that answered):

| | fuzz | `-teq -fallback` | `-chc` |
|---|---:|---:|---:|
| Arrays false | 89 | – | – |
| Arrays true | – | 216 | 4 |
| Loops false | 172 | 1 | 8 |
| Loops true | – | 172 | 146 |

Scored as if all answers were confirmed, Loops would be 817, between UAutomizer (887) and CPAchecker (815) of SV-COMP
2026; with the real rules it is 0, since no answer has a confirmed witness. The drafts below follow the methods.

### A. Violation witnesses of the fuzzer (261 of the 270 false answers)

The fuzzer writes no witness yet (portfolio.py, "Open are the replay of a trace of fuzzing and its witness").
`__VERIFIER_random.c` already records every value it draws with the name of its function, and prints the trace on
`reach_error`. A witness needs the location of each value:

1. **Call sites.** Before compiling, the portfolio rewrites each call `__VERIFIER_nondet_T()` of the `.i` file into
   `__VERIFIER_nondet_T_at(k)`, where `k` is the index of the call site in a table computed on the original text
   (line, column of the closing parenthesis, which is where a `function_return` waypoint is located, and the
   enclosing function); declarations (`(void)`) stay. The harness stores `k` with each sample, as it stores `fn` now.
2. **The witness.** On `unsat`, the recorded values in their order become a `violation_sequence` of format 2.0: one
   segment per value, a `follow` waypoint of type `function_return` at its call site with the constraint
   `\result == v` (`ext_c_expression`, with a cast where the type is narrower than `int` or unsigned), and a final
   segment with the target at the call of `reach_error`, as `yml.Witness` finds it now. Written by portfolio.py
   as `witness.fuzz.yml` (the program's SHA-256, the data model from `-arch`), copied like the witnesses of the other
   methods.
3. **Long traces.** A task that fills an array draws one value per cell, up to 100,000. Whether validators accept
   such witnesses is to be measured; otherwise a cap (e.g. 10,000 values), beyond which the witness has the target
   only, which validators that search on their own may still confirm.
4. **Undefined behavior.** A run whose violation needs a signed overflow is no valid counterexample. Compiling with
   `-fsanitize=undefined -fno-sanitize-recover=all` aborts such runs before `reach_error`, so the fuzzer does not
   answer from them; to check: the 32-bit sanitizer runtime on the workers, and the slowdown.
5. **Cheaper first step:** the target-only witness of `yml.Witness` for the fuzzer's answers, written by
   portfolio.py, to measure how many validators confirm without values.

### B. Measuring what the validators confirm (before the work of A, C, D)

The validators of svcomp-bench-defs (`validate-violation-witnesses-2.0`, `validate-correctness-witnesses-2.0`) on
the witnesses of the portfolio's run: the target-only violation witnesses and the empty correctness witnesses that
`-witness` writes now. The estimate of Oct 13 (above) is for an empty correctness witness only: most of Loops,
almost nothing of Arrays. The measurement decides the order of A, C and D.

### C. Correctness witnesses of `-chc` (150 true answers, 146 of them on Loops)

Plan step 2 above, now with its share: Spacer's model gives the predicates of the loop heads, `Horn` carries the
`:location` of each loop, the arguments of a predicate are the variables in scope at the loop. Translated to C
expressions (challenge 6: casts to `long long` against overflow in the invariant itself, `div`/`mod` only for
non-negative operands, no `store` terms), as `loop_invariant` entries of an `invariant_set`, written by `-chc` to
`witness.chc.yml`. The 48 true tasks that only `-chc` proves (nla-digbench fermat, prod4br, prodbin, and others) have
polynomial invariants of a few variables, the case where this is straightforward.

### D. Correctness witnesses of `-teq -fallback` (388 true answers)

First the empty witness that `-witness` writes now, measured by B. Then the invariants of `-slice` (the trace
equation system of a loop simplified in its context, above) for scalar loops, printed as C expressions; for Arrays
(216 answers) they need quantifiers, which the format lacks (plan step 4).

### Order

B first, since it says how much each of A, C, D can gain; then A (the most answers, the least mathematics), C
(Loops true), and D for scalar loops; quantified invariants for Arrays stay a question of the format.

## Source positions in the C frontend

Implemented (Oct 14-15, 2026): the C scanner locates `while`, `do`, `for` and the names of the error functions
(`Token.Located`, `Parser.Locate`), the loops of the core carry `:location (line column function)` (`c.Parser.while_`),
which reaches `TEQ.loop` and `Horn`; test [examples/c/parsing/location.c](../examples/c/parsing/location.c). A `for`
is a single `while` with the step before `continue`, a `do-while` is `while (first || test)`, loops copied by a `goto`
or inlined by `-teq` share a location, whose invariants are joined by a disjunction.

Open: `if` for branching waypoints, the assertions and nondeterministic calls (`Spec` has no attributes) for detailed
violation witnesses; the printers of the other languages print `:location`, which a validator of SV-LIB may reject.

`-chc` gives the witnesses of SV-LIB and Loops soon; the work specific to TEQ is the extraction of invariants
from proofs, which pays off on arrays only once the format has quantifiers.
