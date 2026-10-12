# Implementing the deduction engine: a concrete plan

Plan of Oct 12, 2026 for [deduction-engine.md](deduction-engine.md), against the code of version 0.42.0. Six
phases, each with the files it touches, the size, the tests that decide it, and what it retires in the lemma
database. Every phase is measured by the same harness (phase 0) and lands only if it loses no proof there.
Code changes happen on a private copy of the repository (worktree `cycles`, later one worktree per phase).

## 0. The harness

Four regression sets, run from a private copy of the jar, one core, exit status read:

| set | what | time |
|---|---|---|
| `mill -i test` | the four groups, 930 tests | 10 min |
| the algorithms | `examples/dafny/algorithms`, 30 files against their `.out` (`pending/runall.sh`) | 5 min |
| the Dafny translations | `benchmarks/sv-comp/dafny/expected.csv`, every fourth row (68 tasks, `pending/candidates/check.sh`), the full 651 rows before a phase lands | 15 min / 2 h |
| MonoCera | the 125 tests with `-unbounded`, counted against the 79 of `summary.md` | 25 min |

A phase is accepted if the four sets lose no proof and no test exceeds twice its time; the gains are recorded
as the lemmas and workarounds it retires (the `Retires` lines below), verified by removing them from the files.

## 1. The re-entrance guard

[reentrance-guard.md](reentrance-guard.md): `Context.active`, `Rewrite.apply(rule)` suspends the rule while its
conditions are evaluated, `Context.key` includes `active`. About fifteen lines in `Context.scala` and
`Rewrite.scala`. Tests: `pending/lower_bound/lb_cmp4.dfy` closes, `pending/nested_module/nested_a.dfy` on the
cocktail program terminates, the former `sum_invs_const` on `nla-digbench/ps2-ll.dfy` terminates; two examples
in `examples/dafny/simplify` (a condition on the rule's own term; a general left-hand side with an `invs`
condition). Retires: the `current(results(...))` left-hand sides of the summaries (bubble, insertion,
cocktail), the open status of the lower bound.

## 2. Canonical forms before matching

All in `Rewrite.scala` and `Simplify.scala`, the context untouched. Four independent steps, each a day or two,
each with unit tests in `test/src/cuvee/test/simplify/RewriteTraces.scala` written *before* the change from the
failing matches of NOTES.md, since several of the "not matched" findings were never isolated to a line.

- **2a. Dependency selection with alternatives.** `Rewrite.instantiate` instantiates an unbound variable
  dependency by the front counter only (`case None => List(front._1)`); make it enumerate all dependencies of
  the expression, front first, so that the for-comprehension of `apply(rule)` backtracks over them. Retires
  `invs_current_counter_other`. Risk: more matches tried; bounded by the number of dependencies.
- **2b. Closed `invs` conditions looked up.** In `Rewrite.conditions`, a closed instance that is an `Invs` is
  looked up among `ctx.known` modulo a canonical form before it is decided: unused dependencies dropped, equal
  dependencies merged, bound variables renamed by position, the body compared after `Simplify.invs`'s own
  normalization. A function `Canon.invs(expr): Expr` in a new file `simplify/Canon.scala` (about 60 lines),
  applied to the instance and to each candidate fact. Retires the fresh variables and identifying equations in
  bubble, selection, insertion, cocktail, first duplicate, row sums (finding 27).
- **2c. Rule variables renamed apart.** In `Rewrite.apply(rule)`, if `rule.vars` intersects the free variables
  of `expr` and of `ctx`, rename the rule's variables fresh (once per rule and command, cached on the rule).
  Retires the naming discipline of the test methods (findings 9, 21) and the error that replaces the goal.
- **2d. The pin in the matcher.** The literal patterns that fail: a literal step `-1` in a dependency
  `⌊counter(s, -1, n)⌋` matched through the context, arithmetic on a bound variable as a store index
  (`a[j - 1 := ...]`), a disjunctive guard, a sum of two rule variables `m + n`, and a higher-order summand. For
  each, a unit test with the pattern and the expression from the example (rewnifrev, insertion_sort, merge,
  cocktail, selection). Then one mechanism: when `matches` fails on a pattern subterm `p` whose free variables
  are bound variables of the pattern or already instantiated, and the expression subterm `e` has the same type,
  abstract `p` by a fresh higher-order variable over its bound variables and record the equation `p == e` as a
  closed condition to decide after the match (the pin, generated). A fallback case at the end of `matches`,
  about 30 lines, plus the decision in `apply(rule)`. Retires the pins of merge, insertion sort, gnome sort,
  cocktail, the stores-ahead-down restatement, `passlen`-style functions; opens the recurrences of TODO.md
  (`a[k - 1]`) to lemmas.

## 3. Congruence closure as the context

`Theory.scala` and `Context.scala`, with `Simplify.var_`, `Simplify.poly` and `Rewrite.rewrite` adapted; the
largest phase, about two weeks.

- **3a. Definitions tried at variables.** `Rewrite.rewrite` returns a variable unchanged; let it try the rules on
  the definition of the variable (`ctx.↑`) when some rule's left-hand side has the definition's head symbol, and
  return the rewritten definition. Ten lines; retires the whole-atom left-hand sides (merge, gnome sort,
  finding 16) and the open trace variables for traces (the definitions are followed in argument positions as
  well).
- **3b. A union-find with congruence closure** `CC` as a `Theory` next to `Facts` and `Diffs`, replacing
  `Chains`: `assume(Eq(l, r))` merges the classes of `l` and `r` and propagates congruence to the parents
  recorded for each node; `repr(e)` the representative, chosen to be a non-variable term if the class has one
  (the definition), a literal if it has one, else the smallest term; `members(e)` for the matcher. Arithmetic:
  a class of integer terms carries the normalized polynomial of its representative, and an equation between two
  arithmetic terms is a linear constraint solved as `Chains.solve` does today, the solution recorded as a
  merge of `x` with its solution term, which inlines into polynomials and, through `repr`, into function
  arguments. `Context.↑` and `Simplify.var_` read `repr`; `Context.used`, `free` and `acyclic` adapt; the
  one-point rule (`Simplify.point`) checks that the variable is alone in its class. `Context.key` includes the
  class structure (its map). About 300 lines new, 150 removed.
- **3c. Implied by classes.** `Context.implied(phi)` holds if `phi` is in the class of `true`, if it is an
  equation of two terms in one class, or by `Diffs` as today; `denied` dually. `Simplify.simplify` then closes
  `s == sorted(a, 0, n' + 1) ∧ n == n' + 1 ⇒ s == sorted(a, 0, n)` without a rule.
- Tests: `examples/dafny/simplify/congruence.dfy` (definitions in argument positions, solutions into arguments,
  two counters identified), is_sorted.dfy verified, the MonoCera `pr2` without `half_even`, nested_sum and
  nested_mult without `mul_eq_cancel`. Risk: the cost of congruence on large goals; the parents table makes a
  merge linear in the parents, and the contexts are copied per position as today, so the structure must be
  persistent (immutable maps, as `Diffs` is).

## 4. State traces with projections

`verify/TEQ.scala` (`loop`), `Simplify.scala` (one projection rule), `Fallback.scala` (the lowering of tuples),
the printers; about a week after phase 3.

- **4a. The state trace.** `TEQ.loop` emits, besides or instead of the per-variable equations, one equation
  `S == trace(tuple(x̄₀), for ⌊K⌋, Zs do s, k, zs :: tuple(F₁(s), ..., Fₘ(s)))` over the tuple of the modified
  variables (`Tuples` of the prelude, the selectors `tupleₘ_i`), the iteration constraint over `⌊K⌋, ⌊S⌋, Zs`
  alone, and `x_i == tupleₘ_i(current(S))`. Behind an option `-teq-state` first, to compare.
- **4b. The projection rule**, a built-in of `Simplify.trace`, not a lemma: a component `i` of a tuple-valued
  trace whose update `Fᵢ` reads the components `J` of the accumulator and no others is the per-variable trace
  `trace(x_i0, for ⌊K⌋, ⌊S⌋ do x, k, s :: Fᵢ[x / sᵢ])` with the other components read from `s`; the simplifier
  applies it to `tupleₘ_i(current(S))` and to `tupleₘ_i(earlier(j, ⌊S⌋))`, so that every lemma of the database
  meets the shape it was written for, with `⌊S⌋` where it had `⌊Y⌋` and `tupleₘ_j(s)` where it had `y`. The
  matcher's synthesis of variable dependencies as maps (`Rewrite.instantiate`) covers the rest: a pattern
  dependency `ys` against `⌊S⌋` with the body reading `tupleₘ_j(s)` is `maps(for ⌊S⌋ yield s :: tupleₘ_j(s))`.
- **4c. Inner loops as values.** In `TEQ.loop`, the summary of an inner loop within a path of the outer body
  becomes `s' == current(S'(s))` with the inner state trace a term over the outer accumulator, which the
  simplifier rewrites as a unit in the context of the outer iteration before the outer trace is distributed;
  the fragments then all bind `s`.
- Tests: `invs_counter_equation.dfy` and `invs_fragments.dfy` without the module `nested`; nested_sum,
  nested_mult and row_sums with the module's lemmas removed one by one; the merge and gnome sort with a lemma on
  the pair. Retires the module `nested` as far as the fragment lemmas go, `results`, the chain lemmas, and the
  summaries' side conditions on fragments (one condition on the inner fold instead). Risk: the Lean semantics
  (`teq.lean`) and the fallback must lower tuples, and the per-variable output is what the SV-COMP databases
  were recorded with, so the comparison runs with both forms.

## 5. Triggers and forward facts

`Simplify.select`, `Simplify.earlier`, `Context.assume`, and the `forward` branch of version 0.30.0 as the
reference (forward rules `:fw`, matched against new facts of `Context.assume`, conclusions recorded one level
deep; it was too slow because `Simplify.nary` re-derived the conclusions in every sibling context). About a
week.

- **5a. Instantiation at indices.** When `Simplify.select(a, j)` or `earlier(j, xs)` is simplified and the
  context has an `invs` over `⌊counter(0, 1, n)⌋` whose body mentions `a[k]` or `earlier(natural(k), xs)`, and
  `0 <= j < integer(n)` is implied by `Diffs`, the body at `j` is assumed in the context of that position. One
  trigger kind, no general forward rules. Retires `not_occurs_selects_def`/`select_not_occurs_selects` style
  pairs, the definitional atoms for constraints in the examples, and closes the checking-loop goals of
  MonoCera whose arrays are resolved (the `above_iterations_def` interference goes with it: the constraint is
  consumed at the index, not abstracted first).
- **5b. Facts about named traces.** Lemmas marked `:facts` on a function of the database (the bounds of `incs`
  and `decs`, `current(sums(x, vs))` with `nonneg_prefix`) are assumed when the term occurs in the goal,
  recorded once per command and term (the memo of 0.30.0, without the sibling re-derivation: the facts are
  attached to the term's e-class of phase 3, not to the context). Retires the cut of `bsearch.dfy`.
- **5c. The disjunctive exit.** In `Simplify.or`, a disjunct `¬(l₁ ∧ ... ∧ lₙ)` that is the negated exit of a
  loop (marked by `TEQ` with an attribute on the implication) is distributed over the other disjuncts when they
  contain atoms that rules of the context have conditions on, one context per literal; otherwise `-split`.
  Retires the two-implication postcondition of first_duplicate.
- Tests: lsearch without its two lemmas, first_duplicate with the equivalence, bsearch without the cut, the
  lower bound with its properties only.

## 6. Equality saturation

Research, after 1 to 5 are measured: an e-graph per goal with the canonical forms of phase 2 as the node
representation, rules applied by e-matching, a nested e-graph per combinator body keyed as
`Context.combinators`, extraction by size. Start from the term bank of phase 3 (a union-find over terms is the
e-graph without the rules). Decide after phase 3 whether the step budget and the rule order still cost proofs;
if the four sets show none, this phase is not needed.

## Order and estimates

| phase | effort | depends on | decides |
|---|---|---|---|
| 1 guard | 1 day | — | the lower bound, the cycles |
| 2 canonical forms | 1 week | — | the summaries' side conditions, the pins |
| 3 congruence closure | 2 weeks | — | is_sorted, `half_even`, whole atoms |
| 4 state traces | 1 week | 3 | the fragments, the module `nested` |
| 5 triggers | 1 week | 3 | constraints at indices, the cut |
| 6 saturation | open | 2, 3 | rule order |

Phases 1 and 2 can start now; 2a to 2d are independent of each other and of 1. Each phase is one commit with
its tests, docs (`doc/simplifier.md`, `doc/teq.md`), the retired lemmas removed from the examples with their
expected outputs regenerated, and a version bump (second digit for 3 and 4).
