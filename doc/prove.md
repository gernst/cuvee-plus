# The deduction engine (`-prove`)

The package [prove/](../src/cuvee/prove) is a second engine for the goals of trace equation systems; its design is
below, the open changes are in [ideas/prove-next.md](../ideas/prove-next.md). `-prove` runs it like
`-simplify` runs the simplifier: the assertions and lemmas with `:rw` are its rules, the other assertions are
simplified under a context and dropped when they become `true`. The package is independent of
[simplify/](../src/cuvee/simplify): what it shares with the simplifier (the polynomials, the clauses, the rules, the
traversal and the matcher) is copied and adapted, not referenced, so that the two engines evolve separately.

## Design

The engine was designed on Oct 12–13, 2026, after the hard algorithms of
[examples/dafny/algorithms](../examples/dafny/algorithms) and the MonoCera tests had been proved with the simplifier
of `-simplify` and many workarounds in the lemmas.

**The findings were symptoms of the engine, not of the method.** Every lemma written for a program followed a dozen
patterns: a left-hand side shaped for one fragment, fresh variables with identifying equations for every `invs`
condition, open trace variables for the traces of the goal, a "pin" for literals and arithmetic on bound variables,
the whole atom of a postcondition as left-hand side, side conditions in the forms of the included modules, the exit
of an outer loop as two implications, variables of the method named apart, and the fragments of inner loops that do
not share facts. Nine of them came from the matcher, the context, or the rewriting strategy, one from the
representation, and only the atoms for quantified hypotheses were partly a design choice. The method, the lookup of
loop shapes in a database of lemmas, was not what the examples strained; the engine that performs the lookup was.

**The representation comes first: one trace per strongly connected component.** A loop is semantically one fold
over its state; a trace equation system is that fold decomposed by projection, one trace per variable. The
decomposition helps where the variables form a layering (counter, index, array, sum): each trace is matched by a
small lemma of its own, which is the compositional reasoning of the paper. It is an obstacle where they do not:
mutually dependent variables (the pointers of a merge, the bounds of a binary search) have individually meaningless
traces over each other, inner loops become fragments over incomparable dependency lists, and dependency lists need
bookkeeping (equal counters, injective selection, arity variants of lemmas). The form that stays partitions the
modified variables by the strongly connected components of their read relation (see [teq.md](teq.md)): a singleton
is a trace as in the paper, a cycle one trace of several accumulators. The component graph is acyclic, so every
trace is a closed term and an inner loop is a value of the outer update; most variables are singletons and are
matched by the database directly. The per-variable traces of a cycle are views, computed on demand, so the lemmas of
the database keep their form, and a lemma may also match a cycle as a whole (the bisection).

**The engine replaces each source of symptoms by a component:**
- *Congruence closure as the context* instead of chains of variable equations and definitions followed on demand:
  a definition is available in every position and both orientations, equal counters are one class, and a pattern
  variable matches a class.
- *Canonical forms and lookup of closed conditions*: alpha-variants and reorderings coincide, so a closed side
  condition is looked up among the facts modulo classes and renaming instead of being simplified again; the fresh
  variables and identifying equations of the lemmas are not needed.
- *A simplex over the rationals* with integer tightening and the bounds of division by literals, instead of
  difference constraints, so arithmetic in the goal's form is decided rather than matched.
- *Forward facts with a trigger discipline* instead of rules on atoms that rarely occur: a lemma `{:fw}` is assumed
  where a term matching its trigger occurs in an assumed fact. The trigger is a term, not a formula; the instance
  names the term as it occurs, so it reaches the classes and the simplex; instances fire no further triggers
  (generation 1), an instance that is known already is skipped, and triggers belong on named terms (a function of
  the database), not on raw trace patterns, which would be matched at every read of every component.
- *Views and one suspension facility* for cycles: a read of a component is matched as the trace of that accumulator
  alone, the others bound over their histories; the rules whose conditions are being evaluated and the components
  whose views are being computed are suspended by the same mechanism, which also replaces the re-entrance guard of
  the simplifier.
- *Case splits and counterexamples* where rewriting stops: a remaining goal is proved by cases on a disjunctive
  premise, a guard of an update that no loop changes, or a remainder by a small literal, and a remaining goal of arithmetic only is refuted by evaluating it at small values.

**Not taken (yet):** equality saturation over an e-graph, which would make the order of rules irrelevant and keep
all forms of a term (a library first, integrated only if rule order still costs proofs); splitting the exit of an
outer loop on demand; firing forward lemmas once per trace definition with a memo per lemma and canonical term
(ideas/prove-next.md), needed before many more forward lemmas, since the firing at every assumed fact is quadratic
in the conjuncts of a premise.

## What differs from the simplifier

- **Congruence closure** ([`Classes`](../src/cuvee/prove/Classes.scala)) in place of the chains of variable
  equations: a persistent union-find over the terms of the facts, where applications are decomposed into their
  arguments and merged by congruence, and everything else (variables, literals, binders, the combinators) is a node
  of its own. The definitions of a variable are the members of its class that are not variables and do not contain
  it (`Context.defs`), in both orientations and transitively (`K == I` identifies two counters, `x == f(y)` with
  `y == z` gives `f(z)`); the matcher tries them when a pattern does not match the variable itself
  (`Rewrite.matches`). Only variables have definitions: a term matched by a member of its class that contains it, e.g.
  `a[k]` by `S.2[k] == a[k]` assumed from a sibling conjunct, is rewritten to a term that contains it again, without
  end. Two literals or two constructors in one class, or a disequation whose sides are in one class, make the context
  inconsistent. `Simplify.var_` replaces a variable by the literal of its class, or by the canonical variable of the
  class (the smallest by name).
- **A simplex** ([`Simplex`](../src/cuvee/prove/Simplex.scala), [`Linear`](../src/cuvee/prove/Theory.scala)) in
  place of the difference constraints: the general simplex over the rationals with bounds (Dutertre and de Moura),
  strict bounds by an infinitesimal, Bland's rule, built per check from the constraints of the context (memoized per
  context, since `Linear.inconsistent` is lazy). On `Int`, a strict comparison is the non-strict one offset by 1 and the
  coefficients are rounded (`Poly.floor`), so `2 * x < 7` bounds `x` by 3; products of atoms are variables of their
  own. An atom `t div k` for a positive literal `k` brings its bounds `k * (t div k) <= t <= k * (t div k) + k - 1`,
  added with the first constraint that mentions it (also when an atom is denied), so the midpoint of a binary search
  lies in its interval, `l <= (h + l) / 2 < h` for `l < h`, without lemmas. Disequations are refuted when the
  constraints determine the difference. The solutions of linear equations for
  a variable (`x` by `40 - n`) are recorded as `solved` and inlined into polynomials, as the chains did.
- **Closed side conditions are looked up** before they are decided (`Rewrite.known`): a closed instance that is
  congruent to a fact modulo the classes holds; an instance with binders, e.g. an `invs`, holds if its canonical form
  equals that of a fact after both are normalized under the classes (`Classes.normalize`, registered subterms
  replaced by the roots of their classes), so the fresh list variables and identifying equations (`Js2 == Js`) that
  the simplifier needs for such conditions are not needed here.
- **Views of traces with several accumulators** ([`Views`](../src/cuvee/prove/Views.scala), see [teq.md](teq.md),
  "Trace equation systems of loops"): the reads of the components of such a trace `S`, `current(S).i` and `⌊S⌋.i` (also through
  `earlier(j, ⌊S⌋.i)`), are markers that the matcher matches modulo their view, the same read of the projection of
  `S` to the component: the trace of that accumulator alone, the other accumulators bound over the histories `⌊S⌋.j`
  of their components (`Views.project`, syntactic). The histories are inert as dependencies, never rewritten in place,
  so the projections do not unfold each other; a component is not projected inside its own view (suspension by the
  loop and the component), and a marker is replaced by its view once that reads no component of `S` (the counter of a
  loop by its value). The `self` of a context, a list of pairs, maps `⌊X⌋`, the histories `⌊S⌋.j` and the history of
  the own component of a projection to their accumulators (`Views.selfOf`, `Views.relation`, by position), so that the
  invariants over the histories bound the accumulators (`Simplify.invariants`). A view is simplified under the facts of
  its position over the variables of the view and of their definitions only (`Context.restricted`), and memoized by
  exactly those facts, so that positions that differ in other facts, e.g. the sibling conjuncts of the goal or a fact
  `lower(a, n, x) <= k` that mentions a parameter of the view, share it soundly; `-debug views`
  reports the misses. The views are memoized by the marker, the bound variables and the
  classes, not by the full context: a view computed under weaker facts is reused.
- **Canonical forms** ([`Canon`](../src/cuvee/prove/Canon.scala)): `Canon.term` renames the variables bound inside
  a term by their depth, sorts the dependencies of combinators (their bound variables permuted along), the cases of
  choices, conjuncts, disjuncts and the sides of equations, so alpha-variants and reorderings coincide; `eq_` decides
  two terms with binders equal by it, which merges cases and dependencies modulo renaming. The traversal renames bound
  variables apart from the context, so positions that differ only by those names recur; the memos of the views, the reads and the facts
  of combinator contexts are keyed by the facts of the position under a renaming of its bound variables by position,
  and store their values under those names, from which the names of the position are restored. The combinator memo
  holds the facts of the inner context, from which the context is built at each position. The simplex checks are
  cached by the set of constraints and disequations (`Linear.checks`). Together they took the transpose from 22 s
  to 7 s.
- **Forward facts** ([`Forward`](../src/cuvee/prove/Forward.scala)): a lemma with `{:fw}` (`requires C ensures φ`,
  not also `{:rw}`) is a fact that is assumed wherever a term that matches its trigger occurs in a fact the traversal
  assumes (the premise of an implication, the denied conclusion, the siblings of a conjunct or disjunct). The trigger
  is the term of `φ` below its boolean, comparison and arithmetic structure with the most variables of the lemma
  (those of `C` only are matched against the facts, as for rules), a term rather than a formula among equals; the
  terms include the dependencies of combinators, outside their binders (a history `⌊S⌋.0`). The trigger is matched
  like the left-hand side of a rule, through definitions and views, so `current(incs(x0, b, ...)) <= b` fires at
  `current(S).0`, and the instance names the term as it occurs, `current(S).0 <= p`, so the fact reaches the classes
  and the linear constraints of the goal's term. The instance is simplified by the rules before it is assumed, so its
  other terms meet those of the goal (the cut of a bisection becomes a partition point). The instances are assumed by
  `Context.assume`, which fires nothing at its own terms (generation 1). A comparison or an equation at a position
  with a polarity also fires the forward lemmas on its own terms when it is decided (`Simplify.forward`), so a goal
  that is a bare atom, `0 <= (x + x * x) / 2`, follows from the instance at its term; the triggers are tried again at the same
  terms as long as instances are added, since one instance may enable another (the invariant `0 <= lo` over `⌊S⌋.0`
  lets the guards of the view of `current(S).0` be rewritten, so its bound matches, in `bsearch_sorted.dfy`); this
  terminates, as the terms are fixed and an instance whose conjuncts are all known is skipped; no lemma fires while
  a trigger is matched.
  `-debug forward` prints the instances.
- **Lemmas over whole cycles** (`Rewrite.matches`): a pattern with several accumulators,
  `trace(l0, h0, for ... do lo, hi, k :: u₀, u₁)`, matches a trace of as many accumulators component by component,
  the initial values pairwise and the results in the context of the update, where the histories of the trace that
  the matched variable defines denote the accumulators, so the iteration constraint holds there; a read
  `current(T).i` or `⌊T⌋.i` of the pattern matches the same read of a variable by its definition; lambdas match
  lambdas of the same arity with their bound variables related. An equation `S == trace(...)` of several
  accumulators is rewritten with `S` as its self, so a rule over the whole cycle can name the trace. The binary
  search over a sorted array is proved so in `bsearch_bisect.dfy`: the rule `bisection` names the trace with its
  probe `M` and guards `G`, `H`, higher-order patterns `G(M(lo, hi))` whose inner function is bound first (from the
  result `M(lo, hi) + 1`) and whose instantiated arguments are beta-reduced (`Rewrite.beta`); a higher-order pattern
  that is not instantiated yet may take several summands of a sum, like a variable, if the sum does not match
  otherwise, so `M(lo, hi) + 1` matches `lo + (hi - lo) / 2 + 1` (`bsearch_safe.dfy`).
- **Rules of the per-variable form** (`Rewrite.combinator`): many rules of the database iterate over the iterations
  and a loop variable, `for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i`, or over the iterations and further
  variables, `for ⌊counter(0, 1, n)⌋, hs do f, k, h`, where `-teq` has the loop variable only. A dependency of the
  pattern equal to an earlier one may take the same dependency of the expression; if the expression has fewer
  dependencies than the pattern, the variables of the rule among the dependencies take the front, and their bound
  variables share its bound variable, which a higher-order pattern `D(k, h)` may then take twice (the abstraction
  ignores the repetition, `D = (k, z) => ...`). A sum of one summand, e.g. `-e`, gives no variable of a pattern
  `v + w` the empty sum 0. A negative literal is the negation of its absolute value among the summands, so the read
  `a[i - 1]` of a pattern matches `a[k + -1]` of the normal form (the recurrences of `aggregation`).
- **Case splits** (`Prove.cases`, `Prove.alternatives`): a goal that remains is proved by cases, each case in a fresh
  context, up to four splits deep; it is dropped if all cases hold and kept as it is otherwise. The first that
  applies of:
  - the first premise that is a disjunction of two or three formulas: the `_cases` rules of `mods`
    (`teq:unsigned`) introduce such premises, `n == zero || integer(n) < 1`, whose cases make the values of the next
    loops known (in-de20 to in-de51);
  - the first atom `c` of a guard of an update whose variables are all free in the goal, not bound by a trace
    (`Prove.conditions`): the cases `c` and `!c`, in which the update has fewer cases, e.g. the guard `y % 2 == 0` of
    a loop that does not change `y` ([diamond.dfy](../examples/dafny/state/diamond.dfy),
    loop-acceleration/diamond_1-1; 0.46.16); `-split` does not reach into the updates of traces;
  - the first remainder `x % m` by a literal `2 <= m <= 4` of variables free in the goal (`Prove.remainders`): the
    cases `x % m == 0, ..., x % m == m - 1`, which the rational simplex does not enumerate, e.g. `y % 2 != 0 ==> y % 2
    == 1` in the odd case of diamond (0.46.16).

  The other splits are left to `-split`, which splits disjunctive premises, if-then-else, and keeps a disjunctive
  conclusion as succedents; the splits of `-prove` are only those that `-split` cannot do, or that need rewriting
  between the levels (the `_cases` rules introduce the disjunction of the next loop).
- **Counterexamples** (`Prove.counterexample`): a goal that remains without traces, lists and other functions than
  those of arithmetic and logic, over at most four integer, natural or boolean variables, is refuted if its body
  evaluates to false at an assignment of small values and the literals of the goal plus or minus 1; it becomes
  `false`, which is answered `incorrect` unless the goal is `:abstract`. The unsafe variants of array-fpi
  leave such goals, e.g. `forall N :: !(0 < N && N <= 536870911)` of brs1f.
- **One suspension facility** (`Context.active`): the rules whose side conditions are being evaluated (the
  re-entrance guard of the simplifier) and the components whose views are being computed, copied into the nested
  contexts; a memoized combinator context takes the suspended set of the position where it is reused.
- Programs, attributes and derivatives are not simplified; `-prove` is for the goals of `-teq`.

## Debugging

`-debug rewrite` prints the rewrite steps and the views (`view <marker> ~> <view>`); `-debug match` the matches that
went through the definition of a variable, the rules on traces whose left-hand side fails on a trace, with the case of
the expression that no case of the pattern covers and the guard that fails; `-debug conditions` the closed side
conditions that fail, with the `self` of the context and the facts on the condition's variables; `-debug forward`
the instances of forward lemmas with their terms; `-debug simplify`
the steps of the traversal; `-rules` reports the rules applied per assertion as with `-simplify`, and the instances of forward lemmas assumed. The compound
expressions of the core cache their hash (`Expr.hashCode`), since the memos and classes hash large terms at every
lookup.

## Checks

`scripts/prove/quick.sh` runs after each change (under 30 s: the state examples except the transpose and the binary
searches against their expected outputs); `scripts/prove/slow.sh` runs on request
or before a commit (the transpose, the unit tests, the 30 algorithms of `examples/dafny/algorithms`
with their exit status, time and remaining goals, as the baseline for the work on them).

## State

Oct 13, 2026: the examples of [examples/dafny/state](../examples/dafny/state) check under `-teq -prove`. With
the database `teq.dfy` alone: single loops, the swap of two arrays, four nested loops without fragment lemmas, the
transpose with one summary lemma, and the syntax example, 1.5 to 5 s. The binary search over a sorted array, with the
array, its bound and the key as parameters, closes by a lemma over the whole cycle, a named bisection with a probe
whose cuts are the partition points (`bsearch_bisect.dfy`, 8 s; `bsearch_safe.dfy` with the probe
`lo + (hi - lo) / 2`), and so does the lower bound of the algorithms (`lower_bound.dfy`, open under `-simplify`,
8 s); the per-component route is kept as a regression test (`bsearch_sorted.dfy` in two layers, 45 s; `bsearch.dfy`
with constant partition points, 8 s). Open: the bisection and the partition points of sorted arrays as a module of
the database, the instances of `invs` by triggers (step 2 of J), the merge and the sorts; see
[doc/prove.md](prove.md) and [TODO.md](../TODO.md).
