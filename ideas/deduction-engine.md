# A deduction engine for trace equation systems, and the representation question

Proposal of Oct 12, 2026, after the hard algorithms of [examples/dafny/algorithms](../examples/dafny/algorithms)
and the MonoCera tests ([doc/array-algorithms](../doc/array-algorithms)). It reconsiders the "principles" of
that document: most of them are not principles of the method but symptoms of the engine, and a few are symptoms
of the representation. It then asks what engine would not have them, and whether the decomposition into one
trace equation per variable helps or hinders compared with a single fold over the whole state.

## 1. Reading the findings as symptoms

The twelve patterns that every lemma written for a program follows (Table 1 of the worked examples), sorted by
what causes them:

| pattern | cause | kind |
|---|---|---|
| a specific left-hand side (bare bound variables synthesized as maps) | first-match ordered rewriting plus synthesis of dependencies | matcher |
| fresh variables and identifying equations for every `invs` condition | closed conditions decided by simplification, not looked up modulo unused dependencies and renaming | matcher |
| open trace variables for the traces of the goal | definitions of variables followed in dependency positions only, not in argument positions | context |
| the pin for literals, arithmetic on bound variables, disjunctive guards | syntactic matching with a fixed list of theories | matcher |
| the whole atom as left-hand side | a variable argument is not expanded by its definition below a function | context |
| arithmetic in the goal's form | decisions by difference constraints only; solutions not substituted into arguments | context |
| side conditions in the forms of the included modules | normal forms depend on the order of rules and modules | strategy |
| no condition on the rule's own term | nested simplification of the instance of a condition (re-entrance) | strategy |
| the exit of an outer loop as two implications | the goal is a formula, case splits are the user's (`-split`) | strategy |
| atoms for constraints and quantified hypotheses | no instantiation of facts at terms; conditions searched syntactically | strategy, partly design |
| variables of the method named apart | rule variables not renamed apart | matcher |
| fragments of inner loops that do not share facts | one dependency list per fragment, unused dependencies dropped | representation |

Nine of the twelve are the matcher, the context, or the rewriting strategy; one is the representation; only the
atoms for quantified hypotheses are partly a design choice (what a lemma may take as a fact). The same holds
for the MonoCera residues: the downward stores-ahead lemma failed on a literal step and a bound-variable
position (matcher), `half_even` exists for a solution not substituted (context), `above_iterations_def` hiding
a constraint is rule order (strategy). The method, lookup of loop shapes in a database of lemmas, is not what
the examples strained; the engine that performs the lookup is.

## 2. What the engine does today, in one sentence each

- **Matching** is syntactic modulo AC of `+`, comparisons as differences, the binding structure of the
  combinators with an injective selection of dependencies, Miller patterns, and the definitions of variables
  on demand in dependency positions; first match wins, no backtracking over the selection of dependencies.
- **The context** is a bag of facts with three theories (facts, chains of variable equations, difference
  constraints); a definition is followed where the matcher asks (`↑`), not in general.
- **Conditions** are instantiated, simplified with all rules, and then decided (closed) or matched against the
  facts (open); matching an `invs` condition builds the fact's combinator context and simplifies its reads.
- **Strategy**: innermost-first ordered rewriting to a fixpoint, with a step budget; the normal form of a term
  is whatever the first applicable rule in module order makes of it.

## 3. The proposal

Five components, each replacing one source of symptoms. They are listed from the most local to the most
far-reaching; the first three could be done within the current architecture.

### 3.1 Congruence closure as the context

Replace the chains, the on-demand `↑`, `replace`, `solved` and the rules extracted from ground equations by a
union-find with congruence closure over the terms of the goal and its facts, with polynomial normalization and
the difference constraints as theories attached to the classes. A pattern variable then matches an e-class, a
definition is followed in every position, both orientations of an equation are available, `K == I` identifies
the two counters, `n == n' + 1` reaches `sorted(a, 0, n)`, and `n == C / 2` with `C % 2 == 0` makes `C == 2 n`
derivable rather than a lemma. Removes: open trace variables, the whole atom as left-hand side, half of
"arithmetic in the goal's form", `half_even`, `mul_eq_cancel`, the stuck goal of `is_sorted`.

### 3.2 Matching modulo canonical forms, with lookup of closed conditions

Canonicalize before matching instead of matching modulo: polynomials in a canonical form (so `i - 1`, `i + (-1)`
and `-1 + i` are one node), combinators with a canonical dependency list (equal dependencies merged, unused
ones dropped, a fixed order with the counter first, bound variables numbered by position), guards as sorted
sets of literals. Then matching is syntactic over canonical forms and e-classes, with backtracking over the
selection of dependencies enumerated as alternatives, and Miller abstraction applied whenever a pattern subterm
over bound variables does not match syntactically (the pin done by the engine). Closed conditions are looked up
in the context modulo the same canonical forms, not re-simplified; rule variables live in their own namespace.
Removes: fresh variables and identifying equations, the pin, specific left-hand sides (the synthesis of a
dependency is one alternative among the matches, no longer the first match), variables named apart, the
literal `-1`, the arity variants of lemmas (a pattern dependency list can be a list variable).

### 3.3 Saturation with a trigger discipline instead of nested rewriting

Conditional rules fire when their conditions are present in the context, in the manner of E-matching with
triggers, rather than by simplifying the condition's instance recursively. A condition that is a formula to be
proved (the quantified step of an induction lemma, a pin) is a separate subgoal, proved by the same engine with
the parent rule suspended (the re-entrance guard of [reentrance-guard.md](reentrance-guard.md)). Facts about
terms that occur are derived forward: the bounds of named monotone traces when `current(incs(...))` occurs, the
body of an `invs` over `⌊counter(0, 1, n)⌋` at an index `j` with `0 <= j < n` in the context (the linear search
and the checking loops of MonoCera without a definition lemma per constraint), the value of a trace variable at
its exit. The disjunctive exit of an outer loop is a case split that the engine makes when a rule on an atom
needs a literal of it. Removes: no condition on the rule's own term, atoms for constraints and quantified
hypotheses, the two-implication postcondition, the cycles of section 1 of the engine ideas, and the dependence
of normal forms on module order, since saturation keeps both the raw constraint and its abstraction.

### 3.4 Equality saturation for the terms

Where 3.3 keeps a context of facts, the terms themselves can be kept in an e-graph: rules add equal nodes
instead of replacing, extraction at the end picks the smallest representative. This makes the order of rules
irrelevant for the result and lets a summary see both `j == current(J)` and `j == integer(nn) + k + 1`. The
combinators are binders, which e-graphs handle with canonical bound variables (3.2) and a nested e-graph per
combinator body with its iteration facts, memoized by its canonical key as `Context.combinators` is today. The
cost is size; a budget on nodes per goal and the current step budget as a fallback. This is the long-term form
of 3.1 to 3.3, not a prerequisite.

### 3.5 The representation: state traces with projections

See section 4. Removes the fragments problem and the two minimal nested-loop files.

## 4. Are trace equation systems helping or an obstacle?

A loop with variables `x̄` is, semantically, one fold over the iterations: `S == trace(s̄₀, for ⌊K⌋ do s̄, k :: F(s̄, k))`
with the state tuple as the accumulator. A trace equation system is that fold decomposed by projection: for
each variable `X == trace(x₀, for ⌊K⌋, ⌊Y⌋, ... do x, k, y, ... :: F_x(x, y, ..., k))`, where the other
components appear as sequences `⌊Y⌋` of dependencies. The decomposition is exact (every projection of a product
fold is a fold over the product's history), and symbolic execution computes it for free.

**Where the decomposition helps.** When the dependencies form a layering (counter, then index, then array,
then sum), each equation is matched by a lemma of its own, the lemma database is a library of small shapes,
and a loop is summarized one variable at a time with the earlier results substituted into the later equations.
This is the compositional and incremental reasoning of the paper, and it is why the single-loop examples and
the SV-COMP arrays go through with no lemma written for the program. A single fold over the state would need
the engine to discover the layering (which components the update of a component depends on) before any lemma
on a counter or a sum could apply; the decomposition is that discovery, done syntactically.

**Where it is an obstacle.** The hard examples are exactly those where the dependency graph is not a layering:

- *Mutual dependencies.* The pointers of the merge, the bounds of the binary search, the position and the
  array of gnome sort are traces over each other (`I` over `⌊J⌋`, `J` over `⌊I⌋`). The equations are
  individually meaningless; the lemma has to reconstruct the product by tying the dependency lists back to the
  traces with open trace variables, and the matcher has to follow definitions in a cycle. The natural object is
  the fold over the pair.
- *Inner loops.* The inner loop's equations become fresh sequences inside the outer iteration constraint, which
  the simplifier distributes into fragments, each with the dependencies it uses; the fragments then range over
  incomparable lists and do not see each other's facts (the two minimal problems), and every summary has to
  reassemble them as side conditions in a fixed order. In the state-trace view the inner loop is one value of
  the outer state's update, `s̄' == current(S'(s̄))`, and all fragments bind the same `s̄`.
- *Bookkeeping.* Equal counters that are not identified, the injective selection of dependencies, unused
  dependencies dropped and later missed, the arity variants of lemmas, `invs_current_counter_other`: all are
  bookkeeping of dependency lists, which a single dependency `⌊S⌋` would not have.

**The answer.** Trace equation systems are the right interface for the lemma database and the wrong sole
carrier of the goal. Keep both forms and let the engine move between them:

- the state trace `S` per loop is the primary object (one counter, one dependency list `⌊K⌋, ⌊S⌋`, all
  iteration constraints over it, the inner loop as a value of the update);
- the per-variable equations are views, `X == π_x(S)` with `⌊Y⌋ == maps(for ⌊S⌋ yield s̄ :: π_y(s̄))`, derived by
  one projection rule whenever the update of `x` mentions only some components, which is when a lemma of the
  database can apply to it; the matcher already synthesizes dependencies as maps (`Rewrite.instantiate`), so
  this is the same mechanism made principal;
- lemmas keep their present form; a lemma over `⌊K⌋, ⌊Y⌋` matches the projection, and a result about `X`
  is a fact about `π_x(S)`, which congruence closure (3.1) relates to the other components.

In the e-graph of 3.4 the two forms are one e-class per variable. What is gained: mutual dependencies need no
tying (both pointers are components of one accumulator, the guard reads both), inner loops are summarized as
units before they are projected (the "interleave generation and rewriting" of the engine ideas), the fragments
problem disappears, and the lemmas for mutually dependent shapes (merge, binary search, gnome, cocktail's
`lo`/`hi`) become lemmas on a fold over a pair with the guard as a higher-order variable, which is what their
summaries are today after all the tying. What is kept: the database, the introduction and acceleration rules,
and the symbolic execution.

## 5. What would change for the examples

| example | today | with 3.1 to 3.3 and 4 |
|---|---|---|
| is_sorted | open, a solution not substituted | closed by congruence closure |
| nested_sum, nested_mult, the two minimal problems | the module `nested` | closed by the shared state, no fragment lemmas |
| merge, gnome sort, lower bound | pins and open trace variables; lower bound open | one lemma on a fold over the pair; lower bound closes with the guard and forward bounds |
| cocktail, insertion, selection, bubble sort | summaries with 7 to 21 side conditions | summaries with the inner fold as one condition |
| first duplicate | postcondition as two implications | the exit split by the engine |
| max_element with `exists` | open, no witness | the witness from the term bank (`argmax` present) |
| counting sort, linear search | atoms for the hypotheses and constraints | instantiation of facts at terms |
| rewnifrev, ifeqn | pins, recurrence not matched | positions as canonical polynomials; the recurrence still needs a closed-form lemma |

## 6. Order of work

The concrete plan is [deduction-engine-plan.md](deduction-engine-plan.md).

1. The re-entrance guard (done first, smallest).
2. Canonical forms before matching and lookup of closed conditions (3.2): the matcher's own file, no change to
   the context.
3. Congruence closure in the context (3.1): replaces `Chains`; the difference constraints stay.
4. State traces with projections (4): a change in `TEQ.loop` and one projection rule, with the per-variable
   form kept as the output of `-teq` for the database and the fallback.
5. Triggers and forward facts (3.3), then equality saturation (3.4) if the budgets of 2 and 3 are not enough.
