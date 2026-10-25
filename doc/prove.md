# The deduction engine (`-prove`)

The package [prove/](../src/cuvee/prove) is a second engine for the goals of trace equation systems; its design is
below, the open changes are in [ideas/prove-next.md](../ideas/prove-next.md). `-prove` runs it: the assertions and lemmas with `:rw` are its rules, the other assertions are
simplified under a context and dropped when they become `true`. The polynomials, the clauses, the rules, the traversal and the matcher were copied from the former simplifier
(`-simplify`, removed Oct 23, 2026) and adapted.

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

## What differs from the former simplifier

- **Congruence closure** ([`Classes`](../src/cuvee/prove/Classes.scala)) in place of the chains of variable
  equations: a persistent union-find over the terms of the facts, where applications are decomposed into their
  arguments and merged by congruence, and everything else (variables, literals, binders, the combinators) is a node
  of its own. The root of a class is a literal before a variable before any other term, variables by name
  (`Classes.rank`, since 0.50.18; before, the root of the larger class), the canonical variable that
  `Simplify.var_` uses. The definitions of a variable are the members of its class that are not variables and do not
  contain it (`Context.defs`), in both orientations and transitively (`K == I` identifies two counters, `x == f(y)` with
  `y == z` gives `f(z)`); the matcher tries them when a pattern does not match the variable itself
  (`Rewrite.matchesExpr`). Only variables have definitions: a term matched by a member of its class that contains it, e.g.
  `a[k]` by `S.2[k] == a[k]` assumed from a sibling conjunct, is rewritten to a term that contains it again, without
  end.
  A rewrite whose result contains its own term modulo the classes, but not as it is, is not applied
  (`Classes.within`, `Rewrite.applyActive`, since 0.50.18): the matcher follows a definition and the simplifier
  replaces a variable by the canonical one of its class, which could undo each other, e.g. `integer(n7)` rewritten
  to `-integer(n25) + ...` with `n25 == n7` on in-de62.2 of SV-LIB (examples/svlib/verify/teq_definitions_class.svlib,
  bugs.md, Fixed); a result that contains its term as it is, e.g. of a rule `f(x) == f(f(x))`, is left to the bound
  on the steps, which reports the rule. The check holds for any cycle through the classes, not only through a
  variable (0.50.17 excluded only the definitions with a variable of the class); it does not make the matcher and the
  simplifier agree on terms other than variables, which normalizing the arithmetic atoms would
  (ideas/prove-next.md, Definitions and canonical variables). Two literals or two constructors in one class, or a disequation whose sides are in one class, make the context
  inconsistent. `Simplify.var_` replaces a variable by the literal of its class, or by the canonical variable of the
  class (the smallest by name).
- **A simplex** ([`Simplex`](../src/cuvee/prove/Simplex.scala), [`Linear`](../src/cuvee/prove/Theory.scala)) in
  place of the difference constraints: the general simplex over the rationals with bounds (Dutertre and de Moura),
  strict bounds by an infinitesimal, Bland's rule, built per check from the constraints of the context (memoized per
  context, since `Linear.inconsistent` is lazy). On `Int`, a strict comparison is the non-strict one offset by 1 and the
  coefficients are rounded (`Poly.floor`), so `2 * x < 7` bounds `x` by 3; products of atoms are variables of their
  own. An atom `t div k` for a positive literal `k` brings its bounds `k * (t div k) <= t <= k * (t div k) + k - 1`,
  added with the first constraint that mentions it (also when an atom is denied), so the midpoint of a binary search
  lies in its interval, `l <= (h + l) / 2 < h` for `l < h`, without lemmas; likewise an atom `t % k` for a
  literal `k != 0` brings its range `0 <= t % k <= |k| - 1` (`range` of
  [remainders.dfy](../examples/dafny/prove/remainders.dfy)). Disequations are refuted when the
  constraints determine the difference. The solutions of linear equations for
  a variable (`x` by `40 - n`) are recorded as `solved` and inlined into polynomials, as the chains did; also a
  solution that is the value of a natural (`c` by `integer(n)`, the final value of a counter, `Linear.integer`, since
  0.50.16), such that the monomials of `c` are those of `integer(n)` (`c * c` and `integer(n) * integer(n)` were
  different atoms of the arithmetic, which the classes do not relate); other equations of a variable with a term that
  is not arithmetic are classes.
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
  lets the guards of the view of `current(S).0` be rewritten, so its bound matches, in the former
  `bsearch_sorted.dfy`, removed Oct 23, 2026); this
  terminates, as the terms are fixed and an instance whose conjuncts are all known is skipped; no lemma fires while
  a trigger is matched. An instance is simplified again each time its lemma fires, with the rewrite steps of the
  command, so many instances of large polynomials can exhaust them; the costs of triggers, conjunctions (which
  `-split` makes lemmas of their own) and variables bound by conditions alone are in teq.md ("What a forward lemma
  costs").
  `-debug forward` prints the instances.
- **Lemmas over whole cycles** (`Rewrite.matchesExpr`): a pattern with several accumulators,
  `trace(l0, h0, for ... do lo, hi, k :: u₀, u₁)`, matches a trace of as many accumulators component by component,
  the initial values pairwise and the results in the context of the update, where the histories of the trace that
  the matched variable defines denote the accumulators, so the iteration constraint holds there; a read
  `current(T).i` or `⌊T⌋.i` of the pattern matches the same read of a variable by its definition; lambdas match
  lambdas of the same arity with their bound variables related. An equation `S == trace(...)` of several
  accumulators is rewritten with `S` as its self, so a rule over the whole cycle can name the trace. The binary
  search over a sorted array is proved so in `algorithms/bsearch.dfy`: the rule `bisection` names the trace with its
  probe `M` and guards `G`, `H`, higher-order patterns `G(M(lo, hi))` whose inner function is bound first (from the
  result `M(lo, hi) + 1`) and whose instantiated arguments are beta-reduced (`Rewrite.beta`); a higher-order pattern
  that is not instantiated yet may take several summands of a sum, like a variable, if the sum does not match
  otherwise, so `M(lo, hi) + 1` matches `lo + (hi - lo) / 2 + 1` (the former `bsearch_safe.dfy`).
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
    a loop that does not change `y` ([diamond.dfy](../examples/dafny/teq/diamond.dfy),
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
  leave such goals, e.g. `forall N :: !(0 < N && N <= 536870911)` of brs1f. The instances are evaluated (`Eval`,
  closed terms of the computed functions over `BigInt` and booleans, naturals by `max(c, 0)`, Euclidean `div` and
  `mod`), not simplified: simplified with the rules, an instance could assume a false premise such as
  `natural(4294967296) == zero` that the classes do not recognize as contradictory, and keep rewriting in that
  context (bugs.md, Fixed, Oct 23, 2026); `Simplify.eq_` decides such equations of natural constants as well.
- **One suspension facility** (`Context.active`): the rules whose side conditions are being evaluated (the
  re-entrance guard of the simplifier) and the components whose views are being computed, copied into the nested
  contexts; a memoized combinator context takes the suspended set of the position where it is reused.
- Procedures are simplified by symbolic execution (`Slice`, see "Programs" below), attributes are not; `-prove` is
  for the goals of `-teq` foremost. Derivatives are computed by the
  rules of dL as in the simplifier (`Simplify.diff`, copied), so the goals of hybrid programs reach the context of the
  engine ([newton.dfy](../examples/dafny/hybrid/newton.dfy), open under the former simplifier).

## Simplification and rewriting

The traversal and the rewrite engine of `-prove`, which the components above extend; the engine was copied from
the former simplifier (`-simplify`, package `simplify`, removed Oct 23, 2026).

- [`Simplify`](../src/cuvee/prove/Simplify.scala) rewrites assertions and
  function definitions to a fixpoint; attributes pass through, procedures go to `Slice` (see "Programs"). Assertions are normalized into clauses (`Normalize`) before
  simplification and after each round of it, which repeats while they change
  (`Simplify.apply`), such that e.g. the equations of `let` are simplified in
  the context; they are dropped if they simplify to `true`.
  `Normalize.lift` lifts `ite` out of the terms of atoms to the level of
  formulas, `A[ite(c, a, b)]` to `ite(c, A[a], A[b])`, but not out of
  binders, derivatives, and `old` inside of `A`; `Split` uses it.
  - All methods take `(config, state, ctx, ...)`. The context `Context` holds the
    facts known at the current position and the rewrite rules, which are
    extracted from the assertions, lemmas, and function definitions with the
    attribute `:rw` (`Rules.from`) and are kept as they are; a definition
    whose body is a match on a parameter gives one rule per case, with the
    pattern in place of the parameter (overlapping patterns are not handled).
    Each rule carries the attributes of its command (`Rule.attrs`), whose
    `:named` names it: the name of a lemma, which the Dafny parser adds, or
    the function of a definition, which `Rules.from` adds; the rules of the
    facts of a context have none.
  - With `-rules`, the context counts the applications of each named rule
    (`Context.applied`), shared by its copies like the steps and fresh for each
    command; the applications while deciding a side condition or a guard count
    only if it holds (`Rewrite.holds`), those while matching a rule only if it
    applies. The counts follow each assertion as structured meta information
    `(set-info :used ((name count) ...))`, also if it simplifies to true and
    is dropped; each `-prove` reports its own applications, such that those
    of several, e.g. before and after `-split`, add up (`scripts/rules.py`).
    Solvers do not receive it, z3 rejects structured values of `set-info`
    contrary to SMT-LIB: the solver sink prints it on
    stderr instead (`Solver.info`). Applications in subterms that are dropped
    later count as well, so that the counts are an upper bound
    ([rules.dfy](../examples/dafny/teq/rules.dfy)).
  - Each round (`once`) simplifies the subterms first and dispatches on the
    built-in functions; afterwards, one rewrite step with the rules of the
    context is tried at the top (`Rewrite.step`), until a fixpoint.
  - Every kind of expression has a helper that takes the simplified
    subterms and builds the result, `and`, `or`, `not`, `imp`, `eq_`,
    `distinct`, `ite`, `upd`, `case_`, `match_`, `trace`, `maps`, `invs`, ...
    The helpers are local normalizations of one constructor: they call each
    other where they build further formulas (e.g. `not` instead of `Not`,
    except in the fallthrough case of `not` itself), and leave out what the
    outer loop already decides. E.g. complementary conjuncts are found by
    `nary`, which simplifies each argument of `and` and `or` assuming the
    others, not by `and` itself.
  - One-point rule: `eq_` turns `x == e` into `true` if `x` is existential
    seen from the current position (`Context.existential`): bound by `exists`
    (`Context.exists`), or by `forall` (`Context.forall`) below an odd number of
    negations and premises (`Context.flip` swaps `universal` and `existential`),
    and `x` occurs nowhere else: not in `e`, not in the facts of the context (`Context.used`,
    which includes the primed variables of derivatives), and `e` has no
    variables bound inside the scope of `x`. `bind` then drops `x`. This
    relies on the context recording all siblings between the binder and the
    equation, which holds for `and`, `or`, `not`, `==>`, and binders only;
    the branches of `ite`, the bodies of `let`, `match`, and `invs`, and
    neutral positions forget which variables are universal and existential
    (`Context.neutral`); the variables of `let`, `match`, and the combinators are
    neither (`Context.bind`).
    Callers that use `eq_` as a decision (`distinct`, `select`, `deps`)
    pass `ctx.neutral`.
  - `trace`, `maps`, and `invs` normalize their dependencies, see
    [teq.md](teq.md).
  - `and` extracts the disjuncts that are common to all conjuncts,
    `(A ∨ C) ∧ (A ∨ B)` is `A ∨ (C ∧ B)`, and `or` dually the common
    conjuncts; this is a local transformation, not a conversion to CNF or
    DNF.
  - The rewrite rules are extracted from formulas
    `∀ xs. if φ then l == r` (also `<==>`, `!p` for `p == false`, and a
    boolean atom `p` for `p == true`); the variables of `r` and `φ` must occur
    in `l` (`Rule.check`).
  - Arithmetic is normalised into polynomials (`Arith`); comparisons and
    equations on `Int` and `Real` become `0 < p`, `0 <= p`, and `0 == p`,
    with `p` primitive, printed with positive coefficients on both sides.
  - Remainders by a literal `k` (`mod`), e.g. of the unsigned arithmetic of
    C, take their coefficients modulo `k`, after remainders modulo multiples
    of `k` among the atoms are replaced by their arguments, also through the
    definitions of variables (`remainders`): `(x % 2^32 + 1) % 2^32` is
    `(x + 1) % 2^32`, `(x % 2^32) % 2` is `x % 2`. A remainder whose argument
    `p`, or its representative with the coefficients centered around 0
    (`representatives`, e.g. `x - 1` for `x + 4294967295`), is known to be in
    `0, ..., k - 1` is that polynomial. The simplex bounds every
    remainder by `0 <= e % k <= |k| - 1` (see above). The update of a
    trace whose results are remainders modulo `k` or the accumulator, and
    whose initial value is in the range, assumes the range of the accumulator
    (`wrapped`), which holds for all its values by induction, such that the
    remainders under the test of the loop are dropped
    ([remainders.dfy](../examples/dafny/prove/remainders.dfy),
    `examples/c/teq/unsigned_*.c`).
  - Derivatives are computed by the rules of dL ([hybrid.md](hybrid.md)).
- [`Rewrite`](../src/cuvee/prove/Rewrite.scala) applies conditional rules
  innermost first, also as a library. Its methods take
  `(config, state, ctx, ...)` as well; matches are substitutions, and side
  conditions are decided by `Simplify.simplify` in the context. Matching
  below the combinators of TEQs is described in [teq.md](teq.md). Sums are
  matched modulo associativity, commutativity and 0 (`matchesSummands`),
  products modulo associativity, commutativity and 1 where they do not match
  position by position (`matchesFactors`, since 0.50.18): `a * k * k` matches
  `k * k` with `a = 1` and `3 * k * k` with `a = 3`, and `a * v` matches
  `3 * k * k` with `v = k * k`, which lets `sum_scale` take the coefficient out
  of a mapped function; a factor 1 only for a term that is a product itself,
  otherwise `a * x` would match every term.
  - A rule is suspended while its left-hand side is matched and its
    conditions are evaluated (`Context.active`, `Rewrite.apply`): the instance
    of a condition is simplified before it is decided or matched, and a
    condition that mentions the rule's own term (`l == current(Lv)` for a
    rule on `current(Lv)`) was rewritten by the rule itself without end; a
    condition that is matched against an `invs` fact builds the context of
    that fact's combinator, whose reads the rule would match again
    ([reentrant.dfy](../examples/dafny/prove/reentrant.dfy),
    [reentrant_invs.dfy](../examples/dafny/prove/reentrant_invs.dfy)). A
    condition that needs the same rule on another instance is not decided.
  - The reads of a combinator context, the values `z == earlier(natural(k), ⌊Z⌋)`
    of its bound variables (`Simplify.iterations`), are normalized by the
    rules without an `invs` condition only (`Rule.plain`), since a rule with
    one would be matched against the `invs` facts and build their contexts in
    turn, through every such rule; and they are cached by the dependencies,
    the bound variables and the definitions of the traces (`Context.reads`),
    since the contexts of a fact are built for every position at which a
    condition is matched against it, with different facts, while the reads
    normalize the same. A context built while a rule is suspended may lack
    that rule's rewrites of its reads and is reused nevertheless.

### Data structures

The context (`Context`, with `Facts`, `Classes` and `Linear`) is described above.

- **`Poly(const, monos)`** with `Mono(factor, atoms)` is the normal form of
  arithmetic, with `Rational` coefficients. `Ring` (in `core.Builtin`) bundles
  the sugar of one type (`Ints.ring`, `Reals.ring`) to read and print
  polynomials.
- **`Poly.sides`** splits a polynomial into its negative and positive parts,
  so that comparisons have positive coefficients on both sides.
- **`Poly.primitive`** scales a polynomial by a positive factor to integral
  coefficients without a common divisor. Comparisons and equations on `Int`
  and `Real` with 0 use it (`Simplify.difference`), since only the sign
  matters there, e.g. `x < 2y + 1.5` becomes `2x < 4y + 3`, and `0.5x == y`
  becomes `x == 2y`.
- **`Rule(params, vars, lhs, rhs, cond)`** is a conditional rewrite rule with
  the type parameters `params` and the variables `vars`, the quantified
  variables of a lemma (`Rule.from`), which must occur in `lhs` or `cond` if
  they occur in `rhs`; other free variables and type parameters are
  constants. The conjuncts of `cond` are taken in their order, instantiated
  so far and simplified: a closed one is decided by the simplifier, an open
  one is matched against the facts of the context (`Context.known`: the
  assumptions and the negated conclusions as given, only double negations
  removed), which instantiates the variables that occur only in `cond`, e.g.
  `n` of `sorted(a, n)`; open comparisons and equations are not searched, since
  there are many arithmetic facts, hence the conjuncts that bind variables
  come first in a lemma (`Rewrite.conditions`). `Rewrite` applies the first rule that matches at the top of
  an expression, a single step, the simplifier traverses and iterates; a
  match is a `Subst` of the type parameters and variables of the rule,
  modulo type instantiation, A/C and 0 of `+` and `-`, comparisons modulo
  moving summands between the sides (as normalized polynomials of the
  difference, where `<` on `Int` is `<=` with 1 added), equations modulo
  symmetry (`a == b` matches `b == a`), and the binding
  structure of `Trace`, `Maps`, and `Invs` ([teq.md](teq.md)).
  Higher-order patterns `F(t₁, ..., tₙ)`, a variable of function type of the
  rule or of a dependency that is a rule variable, applied to distinct bound
  variables of the pattern (Miller's fragment) or to terms whose variables
  are instantiated already, match by abstraction: `F = (z₁, ..., zₙ) => e'`,
  where the bound variables of the expression that correspond to those of
  the pattern are bound, and all occurrences of the instances of the terms
  are replaced by fresh variables, which must occur, e.g. `f = z => z * c + k`
  for `b[k := f(b[k])]` against `b[k := b[k] * c + k]`. A rule variable `F`
  must not capture other bound variables of the expression, but may abstract
  the accumulator; for a variable of a dependency, `instantiate` excludes the
  accumulator. A bound variable of a dependency that is a rule variable is
  chosen among those of the expression. The simplifier beta-reduces the
  instantiated right-hand side. A guard `D(x, h) && φ` of a case of the
  pattern, whose first conjunct is a higher-order pattern, binds `D` to the
  whole guard of the expression; the conjuncts of `φ` are treated like side
  conditions, against the conjuncts of that guard instead of the facts, which
  may bind further variables, e.g. the bound `b` of `F(x, h) <= b`, and the
  closed ones must follow from it (`Rewrite.guard`, `Rewrite.conditions`),
  e.g. the increase `x < F(x, h)` of a monotonic trace; so do the conjuncts of
  other guards that do not match the guard of the expression as a whole. The updates and bodies of combinators
  are matched in the context of the simplifier there (`Simplify.combinator`),
  i.e. assuming the invariants over their dependencies and the iterations of
  loops, and for the right-hand side of `X == trace(...)` also the invariants
  over `⌊X⌋` (`self` of `Rewrite.matchesExpr`), e.g. the test of a loop.
  A function definition with `:rw` whose body is a match on a parameter
  gives one rule per case, the pattern in place of the parameter, and
  the other parameters that clash with pattern variables renamed apart
  (`Rule.from(state, fun, body)`). Overlapping patterns are not handled: a later
  case's rule also fires on arguments that an earlier case matches.

### Facts that the goal does not mention

`Simplify` and `Rewrite` reason backwards from the goal; the forward lemmas (`{:fw}`, see above) are the
exception. A subterm of the goal
is rewritten when the left-hand side of a rule matches it and the rule's
condition holds in the context. The context is consulted for decisions
(`Context.implied`, `Context.denied`, `Rewrite.holds`), and since side
conditions bind variables, also for matching (`Rewrite.conditions`). New facts
are not derived from it.

Some goals hold only because of facts that the goal does not mention, e.g. in
the not-found exit of binary search (see
[prove.md](prove.md)), the bounds of the probes, or
`lastlt < k` and `k < lastgt` for the index `k` of `x` in a sorted array,
whose lemmas never fire, since their conclusions are not subterms of the goal.
Variables of a side condition that do not occur in the left-hand side are
therefore bound by matching the condition against the facts, e.g. `k` of
`a[k] == x`, and the lemma states its conclusion in the shape of the goal
(`Rewrite.conditions`, see `Rule` above). Derived facts are not combined: the
lemma must state `lastlt + 1 < lastgt`, not the two facts `lastlt < k` and
`k < lastgt`.

Otherwise, cuts state such facts in the program,
`assert φ; assume φ;` after a loop, where the assertion is a goal whose atoms
the rewrite rules apply to (see
[bsearch.dfy](../examples/dafny/teq/bsearch.dfy)).
The former Dafny translations of SV-COMP tasks (removed on Oct 23, 2026)
abstracted an iteration constraint by an atom instead, which a second lemma
took as its side condition; the lemma database does
the same, since an iteration constraint as a side condition recurs through the
facts it is matched against (see [teq.md](teq.md)).

## Programs

[`Slice`](../src/cuvee/prove/Slice.scala) simplifies procedures by symbolic execution, statement by statement, and
keeps the structure of the program: its statements, assignments, and if-then-else, whose expressions are simplified
under the facts known at their position. Nothing that is known is forgotten (Oct 25, 2026):

- **Choices.** The context speaks about choices only, fresh variables for the nondeterministic choices of the
  program: the inputs at the entry (parameters, outputs, the global variables of the body, the locals of blocks), havoc
  and the outputs of contracts, the results and modified global variables of calls (`Call.vars`, see
  [datastructures.md](datastructures.md)), the alternatives of a choice where they differ, and the state at the head
  of a loop. Choices never change, so the facts over them hold until the end of the procedure.
- **Values.** Each program variable is bound to its current value, a term over the choices (`Slice.At`). An assignment
  replaces the binding and adds no fact; after the branches of a test, the values that differ are joined by `ite`,
  the facts of the branches by a disjunction with the cases of the test (`join`); after a choice, the values that
  differ are fresh choices that each alternative defines in its disjunct (`merge`).
- **Writing back.** An expression is simplified as its value in the context (`value`, where the `ite` of joined
  values are lifted out of the atoms of formulas, such that each case is decided under its test), and written back
  over the program variables in scope that hold its subterms, those of the expression first (`written`); otherwise it
  stays as written, so the program never mentions a choice. The write-back is syntactic: `x0 + 2` is not written as
  `x + 1` when `x` holds `x0 + 1`.
- **Loops.** The head of a loop has fresh choices for the variables that its body modifies (`.mod`, which includes
  the global variables of calls), constrained by its invariants, also those of its tags; the facts from before the
  loop hold in its body and after it, which adds the negated test unless the body breaks out of the loop.
- **Unreachable code** is dropped: the branch of a decided test, statements after a jump or after a position whose
  context is inconsistent (`assume false`), and a loop that is not entered, of which the assertion of its invariants
  remains, since its head is reached. Statements without effect are dropped from blocks, and a block of one statement
  without locals and attributes is that statement.
- **Context.** One context per procedure (`Slice.simplify` of a `DefineProc`, called by `Prove`), with the rules and
  forward lemmas of the input, one number of steps for the whole procedure, and no polarity. Each kind of statement
  has its helper (`spec`, `assign`, `call`, `block`, `choice`, `if_`, `while_`, `iter`, `ode`, `par`, `jump`); `Ode`
  and `Par` are not simplified, they make the variables that they modify choices.

Examples: [slice_branches.dfy](../examples/dafny/prove/slice_branches.dfy),
[slice_loops.dfy](../examples/dafny/prove/slice_loops.dfy), [slice_calls.dfy](../examples/dafny/prove/slice_calls.dfy).
The invariants of TEQs for the head of a loop, e.g. for witnesses, are not computed yet
([ideas/witnesses.md](../ideas/witnesses.md)).

## Debugging

`-debug rewrite` prints the rewrite steps and the views (`view <marker> ~> <view>`); `-debug match` the matches that
went through the definition of a variable, the rules on traces whose left-hand side fails on a trace, with the case of
the expression that no case of the pattern covers and the guard that fails; `-debug conditions` the closed side
conditions that fail, with the `self` of the context and the facts on the condition's variables; `-debug forward`
the instances of forward lemmas with their terms; `-debug simplify`
the steps of the traversal; `-rules` reports the rules applied per assertion, and the instances of forward lemmas assumed. The compound
expressions of the core cache their hash (`Expr.hashCode`), since the memos and classes hash large terms at every
lookup.

## Checks

`scripts/prove/quick.sh` runs after each change (under 30 s: the state examples except the transpose and the binary
searches against their expected outputs); `scripts/prove/slow.sh` runs on request
or before a commit (the transpose, the unit tests, the 30 algorithms of `examples/dafny/algorithms`
with their exit status, time and remaining goals, as the baseline for the work on them).

## State

Oct 13, 2026: the examples then in `examples/dafny/state` (since Oct 23 in [examples/dafny/teq](../examples/dafny/teq)
and [examples/dafny/algorithms](../examples/dafny/algorithms)) check under `-teq -prove`. With
the database `teq.dfy` alone: single loops, the swap of two arrays, four nested loops without fragment lemmas, the
transpose with one summary lemma, and the syntax example, 1.5 to 5 s. The binary search over a sorted array, with the
array, its bound and the key as parameters, closes by a lemma over the whole cycle, a named bisection with a probe
whose cuts are the partition points (now `algorithms/bsearch.dfy`, 8 s; a variant with the probe
`lo + (hi - lo) / 2`), and so does the lower bound of the algorithms (`lower_bound.dfy`, open under the former simplifier,
8 s); the per-component route was a regression test (`bsearch_sorted.dfy` in two layers, 45 s; `bsearch.dfy`
with constant partition points, 8 s) until Oct 23, 2026, when only the bisection was kept, among the algorithms,
which run on demand (`CUVEE_ALGORITHMS`). Open: the bisection and the partition points of sorted arrays as a module of
the database, the instances of `invs` by triggers (step 2 of J), the merge and the sorts; see
[doc/prove.md](prove.md) and [TODO.md](../TODO.md).
