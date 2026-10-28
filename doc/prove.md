# The deduction engine (`-prove`)

The package [prove/](../src/cuvee/prove) proves the goals of trace equation systems by rewriting with the lemma
database. `-prove` takes the assertions and lemmas with `:rw` as rules and simplifies the other assertions under a
context, dropping those that become `true`; procedures are simplified by symbolic execution (`Slice`, "Programs").
Open changes are in [ideas/prove-next.md](../ideas/prove-next.md), [ideas/canonical.md](../ideas/canonical.md),
[ideas/engine-gaps.md](../ideas/engine-gaps.md), and the consolidation of the engine with what was tried and dropped in
[ideas/engine-consolidation.md](../ideas/engine-consolidation.md).

## Design

A loop is one fold over its state. `-teq` decomposes it by the strongly connected components of the read relation of
its variables ([teq.md](teq.md)): a singleton is a trace, which a small lemma of the database matches; a cycle is one
trace of several accumulators, whose components are read through views. The component graph is acyclic, so every
trace is a closed term and an inner loop is a value of the outer update.

The engine consists of:
- a **context** of three theories: the facts as given, congruence closure with the solutions of linear equations
  (Shostak's combination), and a simplex; terms are kept in canonical form under it, while the matcher sees every
  member of a class;
- **canonical forms of binders** (`Canon`), so that alpha-variants and reorderings coincide and closed side
  conditions are looked up among the facts;
- **forward lemmas** with triggers, for facts that the goal does not mention;
- **views** of the components of cycles and one **suspension** facility;
- **case splits and counterexamples** where rewriting stops.

Not taken, by decision: equality saturation over an e-graph, which would make the order of rules irrelevant and keep
all forms of a term; it is too complicated here (binders in the combinators and views, contextual reasoning per
position, conditional rules decided by the simplex, AC matching), and its gains are reached step by step: rewriting
modulo the classes, AC matching, the canonical forms, the case splits.

## The context

[`Context`](../src/cuvee/prove/Context.scala) holds the facts known at a position, the bound variables by scope, the
rules, and the memos. Each assumed fact goes to all theories:

- **Facts** ([`Theory`](../src/cuvee/prove/Theory.scala)): the assumptions and the denied conclusions, in canonical
  form; inconsistent if `false` is assumed or a fact is both. Side conditions of rules are matched against them
  (`Context.known`), and the memos are keyed by them.
- **Classes** ([`Classes`](../src/cuvee/prove/Classes.scala)): a persistent union-find over the terms of the facts;
  applications are decomposed into their arguments and merged by congruence, everything else (variables, literals,
  binders, combinators) is a node of its own. Two literals or two constructors in one class, or a disequation whose
  sides are in one class, are inconsistent.
  - **Order.** The root of a class is its least member by `Context.order`: a literal before a variable before any
    other term, variables by the depth of the scope that binds them (free variables first) and their position in it,
    then by index and name. Terms are thus written over the variables of the outer scopes and those of a binder over
    the earlier ones, e.g. the count of an inner loop by the bound of its test, the position `i == k + 1` of a loop by
    the counter `k` of its iterations.
  - **Solutions.** A linear equation is solved for its greatest variable if the solution is arithmetic over variables
    (`Classes.solve`, `Poly.solution`), e.g. `x` by `40 - n` for `n + x == 40`; the variable is merged with its
    solution. Solutions are substituted inside arithmetic only (`Classes.substitute`, `Simplify.poly`), so a variable
    keeps its place elsewhere: `a[i := a[i - 1] + 2]` with `i == k + 1` is `a[i := a[k] + 2]`, the shape the lemmas
    match. Nothing else is substituted: equations of traces, reads of traces and arrays, and applications stay members
    of their classes.
  - **Canonical forms.** `Classes.normalize` writes arithmetic in its polynomial normal form with the solutions of its
    atoms, a registered term by its root, and an equation of equal sides as `true`. The simplifier writes a term whose class has a
    literal as its root as that literal (`Classes.ground`), also an application, e.g. the read `a[i]` of the stored value
    `a[i := a[i] + 1]` under `a[i] == 1` (array-fpi/conda); a fact with a literal is no rewrite rule of the context
    (`Context.rule`), so that writing it costs no rewrite step. The simplifier, the context and
    the matcher use this policy through four operations of `Classes` only: `term` (a variable as the root of its
    class), `value` (a leaf of arithmetic with its solution), `fixed` (whether a variable has a literal value), and
    `fact` (a fact in canonical form); a change of the order of roots or of the solutions is a change of `Classes`
    alone. After a merge or a solution, the facts that mention a root it changed are renormalized
    (`Classes.retired`, `Context.renormalize`), the others are canonical already; a fact that becomes `true` keeps its
    form, since the facts are the keys of the memos (`Facts.map`). A solution that depends on its variable through
    the classes is not used (`Classes.acyclic`).
  - **Definitions.** The members of the class of a variable that are not variables and do not contain it
    (`Context.defs`) are its definitions, in both orientations and transitively; the matcher tries them when a pattern
    does not match the variable itself (`Rewrite.alternatives`). A rewrite whose result contains its own term modulo
    the classes, but not as it is, is not applied (`Classes.within`), since the matcher and the canonical forms would
    undo each other.
- **Linear** ([`Linear`](../src/cuvee/prove/Linear.scala), [`Simplex`](../src/cuvee/prove/Simplex.scala)): the general
  simplex over the rationals with bounds (Dutertre and de Moura), strict bounds by an infinitesimal, Bland's rule. On
  `Int`, a strict comparison is the non-strict one offset by 1 and coefficients are rounded (`Poly.floor`), so
  `2 * x < 7` bounds `x` by 3; products of atoms are variables of their own. An atom `t div k` or `t % k` for a literal
  `k != 0` brings the definition of both by SMT-LIB, `t == k * (t div k) + t % k` with `0 <= t % k <= |k| - 1`, which
  bounds the quotient and relates the two, e.g. `t == 2 * n` for `t % 2 == 0` and `t / 2 == n` (array-tiling/pr2,
  tcpy).
  Disequations are refuted when the constraints determine the difference. The tableau is persistent (`Tableau`): a
  constraint is added to the solved tableau of its context and pivots from there, so a check of `implied` costs a
  few pivots. A variable of a new fact that the constraints fix to a value, e.g. `k` of `0 <= k` and `k < n` with
  `n <= 1`, is that value in the classes (`Context.fix`): its value in the solved tableau is the only candidate,
  confirmed if a smaller and a larger value contradict the constraints; so terms over it are decided, also
  nonlinear ones.

A formula follows from the context if denying it makes a theory inconsistent (`Context.implied`).

## Simplification

[`Simplify`](../src/cuvee/prove/Simplify.scala) rewrites assertions and function definitions to a fixpoint;
attributes pass through, procedures go to `Slice`. Assertions are normalized into clauses (`Normalize`) before and
after each round. `Normalize.lift` lifts `ite` out of atoms, `A[ite(c, a, b)]` to `ite(c, A[a], A[b])`, but not out of
binders, derivatives, and `old`; `Split` uses it.

- **Traversal.** Each round simplifies the subterms first and dispatches on the built-in functions, then tries one
  rewrite step at the top (`Rewrite.rewrite`). All methods take `(config, state, ctx, ...)`. In an inconsistent
  context, a formula is decided by its polarity.
- **Unreachable positions** are dropped, by the context that the traversal builds for them anyway: a branch of
  `ite`, a case of `eps` or of `match` whose context is inconsistent, also when its test is not decided; a
  combinator whose body context is inconsistent has no iterations, so a trace is `stop(init)` (the context of a
  single accumulator includes its ranges, `Simplify.wrapped`), a map is `nil`, and invariants hold, also in the
  definitions `X == trace(...)` and `Y == maps(...)`. No term is left unsimplified at an unreachable position, since
  the rules match shapes and such a term would block them elsewhere (a beta-redex for an affine body).
- **Helpers.** Every kind of expression has a helper that builds the result from simplified subterms (`and`, `not`,
  `eq_`, `ite`, `trace`, `maps`, `invs`, ...). Each normalizes its own constructor in one step and builds with the
  other helpers; the outer loop iterates. `nary` simplifies each argument of `and` and `or` assuming the others;
  `and` extracts disjuncts common to all conjuncts, `or` dually.
- **Cases with equal results** are merged (`Simplify.eps`), only these: two results equal as they are, or equal under
  the guard of one of the cases, an equation, in whose context both are brought into canonical form
  (`Classes.normalize`) and compared by `eq_`; the other result is then the value of both cases, e.g. `k` of
  `case k != c => k case k == c => c`, since a result simplified under its guard `k == c` writes `k` as `c`
  ([traces_guards.dfy](../examples/dafny/prove/traces_guards.dfy), copysome2-1). `eq_` expects its arguments in the
  canonical form of its context; the merge is the one place that compares results from the context of another guard.
- **One-point rule.** `eq_` turns `x == e` into `true` if `x` is existential at the position (bound by `exists`, or by
  `forall` below an odd number of negations and premises) and occurs nowhere else: not in `e`, not in the facts
  (`Context.used`), and `e` has no variables bound inside the scope of `x`. The context must record all siblings
  between binder and equation, which holds for `and`, `or`, `not`, `==>`, and binders; other positions are neutral
  (`Context.neutral`). Helpers used as decisions (`distinct`, `select`) pass `ctx.neutral`.
- **Arithmetic.** Terms on `Int` and `Real` are polynomials (`Arith`, `Poly`) with their leaves simplified
  (`Simplify.poly`, `Simplify.leaf`); comparisons and equations become `0 < p`, `0 <= p`, `0 == p` with `p`
  primitive, printed with positive coefficients on both sides (`Poly.sides`, `Poly.primitive`). The difference of the
  sides of a comparison is one conversion (`Arith.difference`), for the simplifier with its leaves simplified in the
  context and for the matcher without (`Rewrite.comparison`).
- **Remainders** by a literal `k` take their coefficients modulo `k`, after remainders modulo multiples of `k` among
  the atoms are replaced by their arguments: `(x % 2^32 + 1) % 2^32` is `(x + 1) % 2^32`; so are the variables
  defined by such a remainder, and those defined by a polynomial that is constant modulo `k`, e.g. `zz % 2` with
  `zz == 2 * count(...)` (`Simplify.remainders`); not those whose definition only reduces to other atoms, which may
  be variables whose definitions lead back. For a small `k` (at most 4), the remainder of `p + c` is that of `p` plus `c`
  if the context fixes the remainder of `p`, e.g. `(i + 1) % 2` is `1` where `i % 2 == 0`: the parity of successors,
  which the rational simplex does not see (mbpr2). A remainder whose argument,
  or its representative centered around 0, is known to be in `0, ..., k - 1` is that argument. A trace whose results
  are remainders modulo `k` or the accumulator, with an initial value in range, assumes the range of its accumulator
  (`wrapped`) ([remainders.dfy](../examples/dafny/prove/remainders.dfy), `examples/c/teq/unsigned_*.c`).
- **Reads after writes** `a[i := v][j]` are decided when `i == j` follows from the context or is denied by it.
- **Cases rather than conditionals.** The conditionals of the update of a `maps` are lifted into cases, as those of
  traces (`Simplify.maps`, `Simplify.choices`), so a map has one form whether its values come from conditionals or
  from the cases of an update; so are choices nested in a term of an update, `R[eps(cᵢ => vᵢ)]` as
  `case cᵢ => R[vᵢ]`, e.g. the read of a map with cases added to an accumulator. A choice in an atom, e.g. the
  element `earlier(j, maps(...))` of a map with cases compared with a value, is lifted out of the atom by the
  polarity of its position: in a goal or a neutral position, e.g. a side condition or the body of `invs`, into the
  conjunction of `cᵢ ==> A[vᵢ]`; among the facts into the disjunction of `cᵢ && A[vᵢ]`, which the case split of
  disjunctive facts and `-split` take apart, so that a definition `a == t[eps(...)]` holds in each case. One function
  lifts at an atom (`Normalize.cases`), for the simplifier (`Simplify.atom`) and for `-split`, which lifts the
  choices of a whole formula by the polarity of its atoms (`Normalize.choices`) besides the conditionals
  (`Normalize.lift`). The guards are complete in context, by the iteration constraint of the loop of the update, also
  where the context at hand does not contain it, e.g. a side condition, so there is no case where no guard holds. A
  choice inside a list or a trace stays, since it is the value of all elements, e.g. `consts(n, eps(...))` of guards
  that do not depend on the iteration (`Normalize.value`).
- **Conditionals in equations** are lifted over them, `ite(c, a, b) == d` is `ite(c, a == d, b == d)`, whose branches
  are decided under the test; they come from the conditionals of programs, while the right-hand sides of the lemmas of
  the database are choices (`if { case 0 <= j < n => ... case !(0 <= j < n) => a0[j] }`, whose guards are exhaustive
  and disjoint). Whether cases and conditionals should leave comparisons and products as well is open
  ([cases-and-folds.md](../ideas/cases-and-folds.md)).
- **Derivatives** follow the rules of dL ([hybrid.md](hybrid.md)); the body of a derivative is simplified with the
  facts that do not mention the variables it differentiates by.

## Rewriting

[`Rewrite`](../src/cuvee/prove/Rewrite.scala) applies conditional rules innermost first; side conditions are decided
by the simplifier in the context.

- **Rules** `Rule(params, vars, lhs, rhs, cond)` come from formulas `∀ xs. φ ==> l == r` (also `<==>`, `!p`, and a
  boolean atom `p`) of assertions, lemmas, and definitions with `:rw` (`Rules.from`); the variables of `r` and `φ`
  must occur in `l` or be bound by `φ` (`Rule.check`). A definition by a match on a parameter gives one rule per case
  (overlapping patterns are not handled); such rules terminate if the recursion is structural, which is why the
  definitions by a `match` of the database are `{:rw}` and those by a test on an integer (`counter`, `consts`) are
  not. Each rule carries the attributes of its command; `:named` names it.
- **Matching** is modulo type instantiation, A/C and 0 of sums (`matchesSummands`), and where that fails, modulo
  their integer constants: the constant `c` of the pattern is cancelled against the constant `d` of the expression if
  `c` lies between 0 and `d`, e.g. `p + 1` matches `3 * k + 2` with `p = 3 * k + 1`, also with `p` bound already, but
  `k + 1` matches no `j` without a constant (`j - 1` would make every term a successor); A/C and 1 of products where they
  do not match position by position (`matchesFactors`), comparisons modulo moving summands, symmetry of equations,
  and the binding structure of `Trace`, `Maps`, `Invs` ([teq.md](teq.md)). Higher-order patterns `F(t₁, ..., tₙ)`
  match by abstraction (Miller's fragment, or terms whose variables are instantiated); the simplifier beta-reduces
  the instantiated right-hand side. A guard `D(x, h) && φ` binds `D` to the whole guard of the expression, and the
  conjuncts of `φ` must follow from it (`Rewrite.guard`). Updates and bodies of combinators are matched in their
  context (`Simplify.combinator`), assuming the invariants over their dependencies, with the same self as in the
  traversal (`Views.self`). An update without cases against one with cases is matched as a whole, and otherwise case
  by case (`Rewrite.update`): the bound variables of the dependencies that are variables of the rule take a value per
  case, the dependency is synthesized as a map whose update has the cases of the expression with these values, e.g.
  `b[p := x₀]` against `case P => a[k := 7] case !P => a[k := 0]` gives `maps(... :: case P => 7 case !P => 0)`; the
  other variables are instantiated alike in all cases, and a guard that reads the accumulator excludes the map like a
  value; a variable in the index of a store takes no value per case, since the keys must stay one sequence, e.g. a
  counter, not `case k != c => k case k == c => c` (copysome2-1, `stores_cases_point`). A term that a pattern does not
  match as it is, is matched by its alternatives, group by
  group, lazily (`Rewrite.alternatives`): the definitions of a variable, the structural view of a component, and only
  then its projected view, which costs a simplification.
- **Side conditions** are taken in order: a closed one is decided, an open one is matched against the facts, which
  binds the variables that occur only in conditions; so conjuncts that bind variables come first in a lemma. A closed
  condition is first looked up among the facts modulo the classes and the canonical forms of binders
  (`Rewrite.known`). The choices that appear once a higher-order variable of the rule, instantiated by an update, is
  beta-reduced and read are lifted out of the atoms of the condition by the simplifier, as in any neutral position
  (`Simplify.atom`, "Cases rather than conditionals"); the cases stay as guards, nothing is merged.
- **The bound on the steps**: every rewrite step counts against a bound per goal and per procedure (`-prove:steps`,
  default 1000, `Context.withRules`), beyond which rewriting is reported not to terminate
  ([steps.dfy](../examples/dafny/prove/steps.dfy)). A fact that equates a term with a literal is no rule of the context
  (`Context.rule`): the classes and the simplex decide it, while as a rule it was applied again at every simplification
  of a term that contains it, e.g. `length(Tmp?) == 5` of the lists of choices (string-1).
- **Suspension** (`Context.active`): a rule is suspended while its left-hand side is matched and its conditions are
  evaluated, so a condition that mentions the rule's own term is not rewritten by it
  ([reentrant.dfy](../examples/dafny/prove/reentrant.dfy)); the components whose views are being computed are
  suspended by the same mechanism.
- **Reads of combinator contexts**, the values of their bound variables (`Simplify.iterations`), are normalized by the
  rules without `invs` conditions only (`Rule.plain`) and memoized (`Context.memo`).
- **Rules of the per-variable form** (`Rewrite.combinator`): a pattern with more dependencies than the expression,
  e.g. the iterations and a loop variable both `⌊counter(0, 1, n)⌋`, takes repeated dependencies of the expression.
- **Lemmas over whole cycles**: a pattern with several accumulators matches a trace of as many component by
  component; reads `current(T).i` and `⌊T⌋.i` match the same reads of a variable by its definition
  ([bsearch.dfy](../examples/dafny/algorithms/bsearch.dfy), the rule `bisection`).
- With `-rules`, the applications of each named rule are counted (`Context.applied`) and reported after each
  assertion as `(set-info :used ((name count) ...))`, on stderr for solvers (`Solver.info`); counts are an upper
  bound ([rules.dfy](../examples/dafny/teq/rules.dfy), `scripts/rules.py`).

## Views

[`Views`](../src/cuvee/prove/Views.scala) (see [teq.md](teq.md)): the reads of the components of a trace `S` of several
accumulators, `current(S).i` and `⌊S⌋.i`, are matched modulo their view, the trace of that accumulator alone with the
others bound over their histories `⌊S⌋.j` (`Views.project`). The histories are inert as dependencies; a component is
not projected inside its own view; a marker is replaced by its view once that reads no component of `S`. A view is
simplified under the facts that mention its variables (`Context.restricted`) and memoized by them.

## Canonical forms of binders

[`Canon`](../src/cuvee/prove/Canon.scala) renames bound variables by depth and sorts dependencies, cases, conjuncts,
disjuncts and the sides of equations, so alpha-variants and reorderings coincide; `eq_` decides terms with binders
by it. The memos of views, reads and combinator contexts are keyed by the facts of the position under a renaming of
its bound variables (`Context.memo`, `Canon.key`). Building such a key hashes the facts, so a memo pays off only where
the key is built rarely and the computation is expensive, once per combinator; memoizing the instances of forward
lemmas by it (0.52.13) doubled the cpu time of SV-COMP Arrays and was removed (ideas/engine-consolidation.md, step 4).

## Forward lemmas

[`Forward`](../src/cuvee/prove/Forward.scala): a lemma `{:fw}` (`requires C ensures φ`) is assumed wherever a term
matching its trigger occurs in an assumed fact (premises, denied conclusions, siblings of conjuncts and disjuncts),
and at a comparison or equation that is decided at a position with polarity (`Simplify.forward`). The trigger is the
term of `φ` below its boolean, comparison and arithmetic structure with the most variables; it is matched like a left
-hand side, and the instance names the term as it occurs, so it reaches the classes and the simplex. Instances fire no
further triggers (generation 1), are simplified by the rules before they are assumed, at every firing (they are not
memoized, see "Canonical forms of binders"), and are skipped if known. Every trigger is tried at every term of every
assumed fact, also without an instance, so a database with fewer forward lemmas is faster: a fact needed only at an
atom of the goal is a rewrite rule on that atom, with the other variables bound by its side conditions (the reads of
`teq:search`).
Their costs are in teq.md ("What a forward lemma costs"). `-debug forward` prints the instances.

## Case splits and counterexamples

- **Case splits** (`Prove.cases`, `Prove.alternatives`): a remaining goal is proved by cases, each in a fresh context,
  up to four splits deep, on the first that applies of: a premise that is a disjunction of two or three formulas
  (e.g. the `_cases` rules of `teq:unsigned`); an atom of a guard of an update whose variables are free in the goal
  ([diamond.dfy](../examples/dafny/teq/diamond.dfy)); a remainder `x % m` by a literal `2 <= m <= 4`; the equation
  `i == j` of a read after a write `a[i := v][j]`. The split on a remainder is on that of the polynomial without its
  constant, which decides those of `p + c` as well (see "Remainders"). Last, the cases `x == l` and `x == l + 1` of an
  integer variable that the premises bound to two values (`Prove.interval`): a lower bound `l` from a premise in which
  `x` has coefficient 1, the upper bound `x <= l + 1` decided in the context of the premises; it evaluates the
  polynomials of higher degree that remain, e.g. `c * c * c == c` for `0 <= c <= k <= 1` (ps2-ps6). Other splits are
  left to `-split`.
- **Counterexamples** (`Eval.counterexample`): a remaining goal over at most four integer or boolean variables,
  without traces, lists, or other functions than those of arithmetic and logic, is refuted if it evaluates to false
  at small values or the literals of the goal plus or minus 1; it becomes `false`, answered `incorrect` unless the
  goal is `:abstract`. Instances are evaluated, not simplified, since the rules decide anything under a premise
  whose contradiction the theories miss.

## Facts that the goal does not mention

The engine reasons backwards from the goal: a subterm is rewritten when a rule matches it and its condition holds;
new facts are derived only by forward lemmas. A lemma whose conclusion is not a subterm of the goal binds its other
variables by matching its conditions against the facts and states the conclusion in the shape of the goal; derived
facts are not combined. Otherwise, a cut states the fact in the program, `assert φ; assume φ;`
([bsearch.dfy](../examples/dafny/teq/bsearch.dfy)).

## Programs

[`Slice`](../src/cuvee/prove/Slice.scala) simplifies procedures by symbolic execution, statement by statement, keeping
their structure; nothing that is known is forgotten.

- **Choices.** The context speaks about fresh variables for the nondeterministic choices only: the inputs at the
  entry, havoc and contract outputs, the results and modified globals of calls (`Call.vars`), differing alternatives
  of a choice, and the state at the head of a loop. Choices never change, so facts over them hold to the end.
- **Values.** Each program variable is bound to a term over the choices (`Slice.At`). After a test, differing values
  are joined by `ite` and the facts of the branches by a disjunction with the cases of the test (`join`); after a
  choice, differing values become fresh choices (`merge`).
- **Writing back.** An expression is simplified as its value (`value`) and written back over the program variables in
  scope that hold its subterms (`written`); the program never mentions a choice. The write-back is syntactic.
- **Loops.** The head has fresh choices for the variables the body modifies (`.mod`), constrained by the invariants.
  The loop is left where its test fails and at its `break`s, joined like the branches of an `if` (`Slice.Exits`)
  ([slice_exits.dfy](../examples/dafny/prove/slice_exits.dfy)).
- **Unreachable code** is dropped: decided branches, statements after a jump or an inconsistent context, and a loop
  that is not entered, of which the assertion of its invariants remains.
- **Context.** One per procedure, with the rules and forward lemmas of the input and one number of steps. Each kind
  of statement has its helper; `Ode` and `Par` make the variables they modify choices.

With `-slice`, which injects the lemma database like `-teq`, the head of a loop is its trace equation system
(`TEQ.head`), built from the values at the entry and simplified in the context before the loop; written over the
program variables in scope, with the remaining choices quantified existentially (`Slice.invariant`), it is attached as
a further invariant, e.g. `cnt == row * wid` ([slice_nested.dfy](../examples/dafny/teq/slice_nested.dfy)).

Examples: `examples/dafny/prove/slice_*.dfy`, `examples/dafny/teq/slice_*.dfy`.

## Debugging and checks

`-debug rewrite` prints the rewrite steps and views; `-debug match` the matches through definitions and the rules on
traces that fail; `-debug conditions` the closed side conditions that fail; `-debug forward` the instances of forward
lemmas; `-debug simplify` the steps of the traversal; `-debug views` the misses of the view memos.

`scripts/prove/quick.sh` checks the examples of `examples/dafny/teq` and `examples/c/teq` against their expected
outputs (20 s each) after each change; `scripts/prove/slow.sh` runs the algorithms of `examples/dafny/algorithms` and
the unit tests on request.
