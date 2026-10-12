# Implementing the deduction engine: work packages

Plan of Oct 12, 2026 for [deduction-engine.md](deduction-engine.md), against the code of version 0.42.4, revised
into packages that can be built and tested in isolation, each in its own worktree, with the dependencies between
them stated. The re-entrance guard of [reentrance-guard.md](reentrance-guard.md) is done (0.42.3) and showed the
way this plan should go: a change is accepted only with a trace that explains the failure it removes, and only
after the harness of package A loses no proof.

## Dependency graph

```
A harness ──┬── B canonical forms ──┬── C closed conditions looked up
            │                       ├── E the pin in the matcher
            │                       └── L e-graph (its node representation)
            ├── D matcher repairs (alternatives, renaming)
            ├── F definitions at variables
            ├── G congruence closure (standalone) ── H arithmetic over classes ── I state traces
            │                                     └── J triggers and forward facts
            ├── K exit splitting
            └── M diagnostics (-probe, budgets)
```

B, D, F, G, K, M have no dependency on each other and can start at once. C and E need B; H, I, J need G; L needs
B and is a long-term alternative to C, E, F and H together.

## A. The harness

Four regression sets from a private copy of the jar, one core, exit status read; a package lands only if it loses
no proof here and no test takes twice its time. The scripts of the guard work (`run.sh`, `algos.sh`,
`sample.sh`, `compare.py` of the scratchpad) should move into `scripts/regression/` as this package.

| set | what | time |
|---|---|---|
| `mill -i test` | the default suite (997 tests, 80 s); `CUVEE_PRINTING=1` after parser or printer changes | 2 min |
| the algorithms | `CUVEE_ALGORITHMS=1 mill -i test`, or the 30 files with `-test` | 5 min |
| the Dafny translations | every fourth row of `benchmarks/sv-comp/dafny/expected.csv` (68 tasks), all 651 before landing; compared with the current main's jar, since expected.csv predates it | 15 min / 2 h |
| the C benchmarks | `./benchmark xml/cuvee.xml -r SV-COMP27_unreach-call -t C.unreach-call.Arrays` and `Loops` at `-T 60s` with the jar installed in the checkout, compared with the latest 60 s run of main (`compare.py`) | 15 min |
| MonoCera | the 125 tests with `-unbounded` against the 79 of `summary.md` | 25 min |

## B. Canonical forms (`simplify/Canon.scala`, new, standalone)

Pure functions on `Expr`, no context, no rules: `Canon.poly` (a polynomial with sorted monomials and literal
constants, so that `i - 1`, `i + (-1)` and `-1 + i` are one term), `Canon.combinator` (equal dependencies
merged, unused ones dropped except the counter, a fixed order with the counter first, bound variables renamed by
position), `Canon.guards` (the conjuncts of a guard as a sorted set of literals, negations in normal form).
Testable alone: idempotence, equality of α-variants, the examples of the dependency lists of NOTES.md. About
150 lines, three days. Used by C, E, L and by the hashing of G. Retires nothing by itself.

## C. Closed conditions looked up (`Rewrite.conditions`)

A closed instance that is an `Invs`, an equation of lists, or an atom is looked up among `ctx.known` modulo
`Canon` before it is decided by simplification. One function, about 30 lines, plus unit tests in
`RewriteTraces.scala` for the 21st condition of the cocktail summary and the flags fact of first_duplicate.
Retires the fresh variables and identifying equations of six example files (the summaries shrink by a third).
Needs B.

## D. Matcher repairs (`Rewrite.instantiate`, `Rewrite.apply`)

Two independent fixes with unit tests written first from the findings:
- `instantiate` offers only the front counter for an unbound variable dependency (`case None => List(front._1)`);
  offer all dependencies, front first, so the for-comprehension of `apply` backtracks (finding 1; retires
  `invs_current_counter_other`).
- rule variables renamed apart from the free variables of the goal, once per rule and command (findings 9, 21;
  retires the naming discipline of the test methods and the error that replaced the goal).
Two days. No dependencies.

## E. The pin in the matcher (`Rewrite.matches`, fallback case)

For each literal pattern that fails (the step `-1` of a counter dependency through the context, a store index
`i - 1`, a disjunctive guard, a sum `m + n` of two rule variables, a higher-order summand), first a unit test with
the pattern and the expression of the example; then one mechanism: when a pattern subterm over bound or
instantiated variables fails to match an expression subterm of the same type, abstract it by a fresh
higher-order variable and record `p == e` as a closed condition decided after the match. About 40 lines.
Retires the pins of merge, insertion sort, gnome sort, cocktail, the stores-ahead-down restatement, and opens the
recurrences on `a[k - 1]` to lemmas. Needs B for the arithmetic cases (the equation `p == e` is decided on
canonical polynomials).

## F. Definitions at variables (`Rewrite.rewrite`)

A variable with a non-variable definition in the context gets the rules tried on its definition, when some
rule's left-hand side has the definition's head symbol, and is replaced by the rewritten definition. Ten lines,
one day, tests on merge and gnome sort with the whole-atom left-hand sides replaced by rules on
`current(trace(...))`. Retires the whole-atom pattern and the open trace variables for traces. No dependencies;
subsumed by G later, but cheap now.

## G. Congruence closure, standalone (`simplify/CC.scala`, new)

A persistent union-find over terms with congruence propagation, as a `Theory` next to `Facts` and `Diffs`:
`assume(Eq(l, r))` merges, `repr(e)` the representative (a non-variable definition if the class has one, a literal
if it has one, else the smallest term), `members(e)`, `implied(Eq(l, r))`. Built and tested entirely alone, on
terms without any context: merge, congruence through parents, persistence of copies (immutable maps as `Diffs`),
cost on goals with a thousand terms. Then, as a second step in the same package, wired into `Context` in place of
`Chains.replace` and `Chains.chain`: `Context.↑` and `Simplify.var_` read `repr`, `used`, `free`, `acyclic` and
the one-point rule adapt (`Simplify.point` checks that the variable is alone in its class), `Context.key`
includes the class map. About 300 lines new, 150 removed, two weeks. Retires open trace variables, the whole
atom, equal counters not identified. The integration step is the risky part and is measured by the harness
before H starts.

## H. Arithmetic over classes (`CC` with `Poly`)

A class of integer terms carries the normalized polynomial of its representative; an equation between two
arithmetic terms is a linear constraint solved as `Chains.solve` does today, recorded as a merge of the variable
with its solution, which reaches function arguments through `repr`. Tests: is_sorted.dfy verified; `pr2` of
MonoCera without `half_even`; nested_sum and nested_mult without `mul_eq_cancel`. One week. Needs G.

## I. State traces with projections (`TEQ.loop`, `Simplify.trace`, `Fallback`)

Behind an option `-teq-state` first: one trace of the tuple of the modified variables per loop, the iteration
constraint over `⌊K⌋, ⌊S⌋`, `x_i == tupleₘ_i(current(S))`; a built-in projection rule in `Simplify.trace` that turns
a component whose update reads the components `J` into the per-variable trace with the others read from `s`, so
that the lemmas meet the shapes they were written for; inner loops as values `s' == current(S'(s))` simplified as
units in the outer iteration. Tests: the two minimal nested-loop files without the module `nested`, nested_sum and
nested_mult with the module's lemmas removed one by one, merge and gnome sort with one lemma on the pair; the
Lean printer and the fallback lower tuples. One week after G, since the projections are equations between classes.
Retires the fragment lemmas of `nested`, `results`, the chains, the fragment side conditions of the summaries.

## J. Triggers and forward facts (`Simplify.select`, `Simplify.earlier`, `Context.assume`)

Three sub-packages, each alone:
- instantiation at indices: when `a[j]` or `earlier(j, xs)` is simplified and the context has an `invs` over
  `⌊counter(0, 1, n)⌋` whose body reads `a[k]` or `earlier(natural(k), xs)`, and `0 <= j < integer(n)` is implied,
  assume the body at `j` at that position (retires the definitional atoms for constraints, the lsearch pair, and
  the `above_iterations_def` interference);
- facts on named traces: lemmas marked `:facts` on a function of the database assumed when the term occurs,
  memoized per command and term (the `forward` branch of 0.30.0 without its sibling re-derivation; retires the
  cut of bsearch);
- a trigger table in the context, so that the first two do not scan the facts at every read.
One week. Needs G for the memo by class; the first sub-package can be prototyped without it.

## K. Exit splitting (`Simplify.or`)

A disjunct `¬(l₁ ∧ ... ∧ lₙ)` that is the negated exit of a loop, marked by `TEQ` with an attribute, is
distributed over the other disjuncts when they contain atoms that rules of the context have conditions on, one
context per literal. Two days. Retires the two-implication postcondition of first_duplicate. No dependencies.

## L. E-graph (`egraph/`, new package, standalone)

A library independent of the simplifier: hash-consed nodes over `Canon` forms, classes with a union-find,
rebuilding (congruence), e-matching of patterns with pattern variables bound to classes, extraction by size, a
budget on nodes. Built and tested alone on arithmetic and uninterpreted terms, then with the combinators as
binders: canonical bound variables (B) and a nested e-graph per combinator body carrying its iteration facts,
memoized as `Context.combinators` is. Integration last, as a transform `-saturate` that takes the goal and the
rules of the context, saturates within the budget, and extracts; the ordered rewriter stays as it is. Decides
whether rule order still costs proofs after C to H; if the harness shows none, L stays a library. Open-ended;
the library alone is two weeks and useful for G's representation as well.

## M. Diagnostics (`-probe`, budgets, timeouts)

Independent of everything: `-probe <lemma>` reports the first side condition of a named rule that fails on a goal,
with the facts it was matched against, and which part of a left-hand side did not match; a separate step budget
for the evaluation of conditions whose exhaustion leaves the condition undecided instead of aborting the command
(remedy 3 of the TODO entry); a timeout that reports the goal it was working on. One week. Retires the probe
files and pair runs of `pending/`.

## Order

A first, then B, D, F, G, K, M in parallel worktrees; C and E after B; H, I, J after G has landed and is measured;
L when the rest is in and the harness still shows proofs lost to rule order. Each package is one commit with its
tests, its docs (`doc/simplifier.md`, `doc/teq.md`), the retired lemmas removed from the examples with their
expected outputs regenerated, and a version bump.
