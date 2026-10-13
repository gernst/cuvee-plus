# Implementing the deduction engine: the representation first, then the packages

Plan of Oct 12, 2026 for [deduction-engine.md](deduction-engine.md), revised Oct 13, 2026 after the first milestone
of the package `prove` (see [deduction-engine-implementation.md](deduction-engine-implementation.md) for the record,
the decisions taken and the log). The representation comes first: a loop is a fold over its state, the per-variable
trace equations of the paper are projections of it, computed on demand when a lemma needs one. The revision takes
in what the implementation taught: the state form is partitioned by the strongly connected components of the
loop's variables, and the tuples of the prelude are a first version of a syntax in which the combinators bind
several accumulators. The engine packages that follow are independent of each other where stated. The rule for all
of this stands: a change lands only with the trace that explains the failure it removes, and only after the quick
check loses no proof.

## 1. The representation

### 1.1 Why first

Section 4 of [deduction-engine.md](deduction-engine.md) found that the hard cases are those where the
decomposition into one equation per variable is wrong by construction: mutually dependent variables whose
equations are individually meaningless, inner loops whose equations become fragments over incomparable
dependency lists that do not see each other's facts, and the bookkeeping of dependency lists (equal counters,
injective selection, unused dependencies, arity variants). The implementation confirmed the diagnosis: the state
form proves the five nested examples without a fragment lemma, resolves the swap through one lemma on earlier
stores, and reaches the same point as the per-variable proof on the binary search. The reason is a single property:
no trace depends on another one, so every trace is a closed term and an inner loop is a value of the outer update
(see the conclusion of [state-trace.md](state-trace.md)).

### 1.2 The form that stays: one trace per strongly connected component

The full state tuple pays for its uniformity: every read of a component is a selector application that the engine
must recognize as a marker, suspend, key and replace, and the existing lemmas with typed dependencies need
polymorphism for the list of states. The refinement keeps the property that matters and drops the uniformity.
`TEQ.loop` builds the read relation of the body over the modified variables, where a variable depends on what its
results read and on what the case guards read (the guards are shared by all components), takes the strongly
connected components with `util.SCC` (which also orders them topologically), and emits one trace per component in
that order:

```
K == counter(0, 1, n)
X₁ == trace(x₁₀, for ⌊K⌋, Z̄ do x₁, k, z̄ :: ...)                              -- a singleton component: as in the paper
S₂ == trace(tupleₘ(x̄₂₀), for ⌊K⌋, ⌊X₁⌋, Z̄ do s, k, x₁, z̄ :: ...)             -- a cycle: a tuple trace over the earlier histories
invs(for ⌊K⌋, ⌊X₁⌋, ⌊S₂⌋, Z̄ check k, x₁, s, z̄ :: guard ∧ (B₁ ∨ ... ∨ Bₚ))
```

Since the component graph is acyclic, every trace is a closed term over the number of iterations, the choices and
the earlier histories; nested loops are substituted as today (`StateTEQ`, `Path.depth`), outermost loops keep
their definitions as equations. All variables in one component is the state form of today, all singletons is the
per-variable form, which is exactly the case where that form had no cycles and worked: the per-SCC form is the
finest decomposition without recursion. Most variables are singletons (counters, indices, sums over the input,
arrays written at the index), so most traces are matched by the database directly, with its typed dependencies, and
print as before; views, suspension and the positional relation are confined to the real cycles (the two arrays of the
swap with the temporary, the bounds of the binary search, the pointers of a merge). The relation is syntactic, hence
conservative (a read under a guard that never fires merges components). Choices stay dependencies of the variables
that use them. The fragments that the distribution of the constraint produces are harmless now, since no fresh
sequences are involved, only closed terms.

### 1.3 Views, as implemented (revised Oct 13, night, for traces of several accumulators)

The two halves of a view are treated differently. The *projection* of a trace to a component is syntactic (the
component's accumulator alone, the others bound over the histories `⌊S⌋.j`) and the matcher performs it implicitly:
a pattern `current(trace(...))` or `⌊trace(...)⌋` meets a read `current(S).i` or `⌊S⌋.i` and is matched against the
projection directly, without simplifying it (`Views.structural`), where the sibling histories are dependencies that
the pattern need not mention. The *normal form* of a component (the fold into `stores`, the counter evaluated, the
reads of the other components resolved) is a rewriting, not a match, so it stays explicit, computed once per loop
and component with suspension and memoized (`Views.projected`); the matcher falls back to it when the structural
match fails. The description of the tuple form below is kept for the record:


For a tuple trace, a read of a component (a selector applied to the current or an earlier value of the trace, also
through a bound variable of a combinator over its history, or a map of one) is a marker that the matcher matches
modulo its view, the simplified projection of the trace to that component, with the other components read from the
history as a dependency and the own component read from the accumulator (`Views.project`). A component is not
projected inside its own view (`Context.active`, keyed by selector and number of iterations), a marker whose view
reads no component is replaced by it in place, and while a view is simplified or matched the context carries the
selector being projected (`Context.projection`), from which each projection trace derives the relation "the read of
the component from the state is the accumulator" by position (`Views.relation`), which `Simplify.invariants` applies
to the invariants over the history. Views are simplified under and memoized by the facts of the position that mention
their variables (`Context.restricted`). The per-variable equations are never stated; nothing is mutually recursive.

### 1.4 First-class syntax: combinators with several accumulators

The tuples of the prelude are the semantics (a trace of products, immediate in Lean and in the fallback) but a poor
syntax for the engine. Once the merge and the sorts have shown what the lemma language needs from cycles, the
trace of a cycle should bind its accumulators in the core rather than wrap them in a tuple, which removes most of 1.3
by construction: the components are bound variables, not selector applications, so a read of a component is a
variable, the relation of a projection is trivial, suspension keys on the trace and a position, and matching a
per-variable lemma against a component is choosing the component and treating the others as dependencies, done by the
matcher like its selection of dependencies today (`Rewrite.combinator`). The sketch, signatures only:

```scala
// trace(x̄ := ē₀, for deps do ȳ :: ē): the trace of the accumulators accs, one initial value and one result per
// accumulator, where a result is a guarded expression (Eps) over the loop's shared guards as in the paper, so that the
// simplifier merges the cases of each component on its own; the dependencies are lists as today, one bound variable
// each; the type is Trace<(T₁, ..., Tₘ)> over the existing sorts Trace<a> and tupleₘ, Trace<T> for one accumulator:
// the tuple lives in the type only, no term of tuple type is ever built in a goal
case class Trace(inits: List[Expr], deps: List[Expr], accs: List[Var], bound: List[Var], results: List[Expr]) extends Expr

// unchanged: a map has one result and a constraint one body, their dependencies are lists, one bound variable each
case class Maps(deps: List[Expr], bound: List[Var], update: Expr) extends Expr
case class Invs(deps: List[Expr], bound: List[Var], body: Expr) extends Expr

// the history and the last value of a trace, per component, as core nodes typed structurally (the type checker reads
// the component type Tᵢ off the tuple type of the trace, since the combinators are built in): the history of a trace
// with m accumulators is m lists ⌊S⌋.1, ..., ⌊S⌋.m of the ordinary type List<Tᵢ>, which are m dependencies of equal
// length wherever the state is read, so no list of tuples exists and the functions on lists are untouched; no family
// of selectors is declared, which is what the tuple terms of today cost
object Butlast: def apply(trace: Expr, i: Int): Expr
object Current: def apply(trace: Expr, i: Int): Expr
```

**Types.** No new sort and no family of sorts: `Trace<a>` and `List<a>` stay as declared in `core.dfy`, and a cycle
trace has the type `Trace<tupleₘ<T₁, ..., Tₘ>>` with the tuple sorts of the prelude, which is the honest description
of its values (a trace of states; in Lean a trace of a product). The constructors `stop` and `step` instantiate `a`
with the tuple type but are applied only in the Lean proofs, never in goals. The one consequence is on the output
side: a goal quantifies over `S: Trace<(int, int)>`, so the output language needs the tuple sort, which Dafny has in
its prelude and SMT-LIB output from C input gets declared ahead of the goal if a trace survives to the output at all
(the fallback lowers it into one function per component before a solver sees it). A family `Traceₘ` indexed by the
arity, as the tuples are, was rejected: it would need a family of observers `currentₘ_i`, `butlastₘ_i` and put the
database on `Trace₁`; a variadic sort would need variadic constructors in `Con`.

A trace with several accumulators is used only where a cycle needs it (section 1.2); the loop as a whole still has
one trace per component in topological order. The per-variable form is the case of one accumulator, the state form
of today the case of one trace with all accumulators, so both are instances. The history of a cycle trace flattens
into its component lists wherever it is a dependency, which is how `Maps` and `Invs` compose with it without any
change: a map that would yield several values is several maps, and the synthesized `maps(for ⌊S⌋.j yield h :: h)` of
the matcher is `⌊S⌋.j` by `maps_identity`. The projection of a cycle trace to a component becomes syntactic: the
co-accumulators in the component's result are replaced by fresh bound variables over the corresponding histories
`⌊S⌋.j`, and a lemma on one accumulator matches the result like any per-variable trace; of the views only this
construction remains, without selectors, closedness check or a relation to carry. `Eps` and `Upd` stay as they are,
per component; `Type.dependencies` is unchanged; the parsers and printers of Dafny, Boogie and SMT-LIB get the syntax
of several accumulators and of `⌊S⌋.i`, `current(S).i`, the Lean printer prints products, `Fallback` one function per
accumulator. Estimated a week across the core, the four frontends, the two engines and the fallback, to be done when
the lemma language asks for it, not before.

Accumulator patterns in lemmas (the former step S5) come with it for free. Estimated a
week across the core, the four frontends, the two engines and the fallback, to be done when the lemma language asks
for it, not before.

### 1.5 Steps and tests

| step | what | state |
|---|---|---|
| S1 | the joint trace over the tuples of the prelude (`StateTEQ`, `-teq-state`), closed for nested loops | done (0.43.0, 0.43.1) |
| S2 | views in place of projection rewrites, with suspension | done |
| S3 | the positional relation of a projection, the definitions through the classes, views memoized by relevant facts | done |
| S4 | inner loops as values by the closed substitution | done |
| S5 | traces per strongly connected component (`util.SCC` in `StateTEQ`; the read relation includes the guards) | done Oct 13: the ten state examples unchanged, the swap with `I` a plain counter, `S` the two arrays, `T` after them |
| S6 | the merge and the sorts in the state form, lemmas over cycles; what the lemma language needs | after S5 |
| S7 | combinators with several accumulators in the core (1.4), the tuples of the prelude retired from the goals | done Oct 13 on the branch `accumulators` for the core, Dafny and the engine of `-prove` (views as syntactic projections, `self` a list, the tuple selectors gone); the other frontends (Boogie, SMT-LIB, SV-LIB) and the Lean printer done Oct 13 (0.46.6); open: lemmas over whole cycles in the matcher |
| S8 | `-fallback` for tuple or multi-accumulator traces, the tuples for C input, the C benchmarks with a cleaned-up lemma selection | `-fallback` for traces of several accumulators done Oct 13 (0.46.6, one function per accumulator); the benchmarks only when the user asks |

What it retires: the module `nested` as far as the fragment lemmas go, `results`, the chain lemmas of row sums,
the fragment side conditions of all summaries, `invs_current_counter_other`, the identification of equal
counters, and the "open trace variable" pattern for tying dependencies to traces; after S5 also the polymorphism of
lemmas over another dependency except within a cycle.

## 2. The engine packages

Independent of each other unless stated; A first. Those marked (joint) are easier after section 1 and should
wait for S3; the others can start now in parallel worktrees.

### A. The harness
**State:** done in a quick form: `scripts/prove/quick.sh` after each change, `slow.sh` and `compare.sh` on request; the full suite and the benchmarks are not run between changes (the user iterates quickly).
Four regression sets from a private copy of the jar, one core, exit status read; a package lands only if it
loses no proof and no test takes twice its time. The scripts of the guard work (`run.sh`, `algos.sh`, `sample.sh`,
`compare.py`) move into `scripts/regression/`.

| set | what | time |
|---|---|---|
| `mill -i test` | the default suite (997 tests, 64 s); `CUVEE_PRINTING=1` after parser or printer changes | 2 min |
| the algorithms | `CUVEE_ALGORITHMS=1 mill -i test` | 5 min |
| the Dafny translations | every fourth row of `benchmarks/sv-comp/dafny/expected.csv` (68 tasks), all 651 before landing, compared with main's jar | 15 min / 2 h |
| the C benchmarks | `./benchmark xml/cuvee.xml -r SV-COMP27_unreach-call -t C.unreach-call.Arrays` and `Loops`, `-T 60s`, the jar installed in the checkout, against the latest 60 s run of main | 15 min |
| MonoCera | the 125 tests with `-unbounded` against the 79 of `summary.md` | 25 min |

### B. Canonical forms (`simplify/Canon.scala`, standalone)
**State:** done in `prove/Canon.scala`: canonical keys of the memos, the canonical form of terms for the lookup of conditions with binders and for `eq_`; the matcher itself is modulo AC as before.
Pure functions on `Expr`: canonical polynomials (`i - 1`, `i + (-1)`, `-1 + i` one term), canonical combinators
(equal dependencies merged, unused dropped except the counter, a fixed order with the counter first, bound
variables renamed by position), guards as sorted sets of literals. Tested alone for idempotence and α-variants.
150 lines, three days. Used by C, E, L and the hashing of G.

### C. Closed conditions looked up (`Rewrite.conditions`)
**State:** done (`Rewrite.known`, modulo the classes and the canonical forms, facts of the same shape).
A closed instance that is an `invs`, an equation of lists or an atom is looked up among `ctx.known` modulo
`Canon` before it is decided. 30 lines plus unit tests from the 21st cocktail condition and the flags fact of
first_duplicate. Retires the fresh variables and identifying equations of six files. Needs B. Less needed
after S4, since the fragments that these conditions pick up no longer exist, but still right for conditions on
the iteration constraints.

### D. Matcher repairs (`Rewrite.instantiate`, `Rewrite.apply`)
**State:** open; the alternatives over dependencies are superseded by the views.
Rule variables renamed apart from the goal's free variables (findings 9, 21). The alternatives over dependencies
for an unbound variable dependency (finding 1) are superseded by S3's projection-aware instantiation; do them
only if S3 slips. Two days.

### E. The pin in the matcher (`Rewrite.matches`, fallback case)
**State:** open; expected to be pulled by the merge and the sorts (S6).
A unit test per failing literal pattern (the step `-1` through the context, the store index `i - 1`, a
disjunctive guard, `m + n`, a higher-order summand), then one mechanism: a pattern subterm over bound or
instantiated variables that fails to match is abstracted by a fresh higher-order variable with `p == e` as a
closed condition decided after the match. 40 lines. Retires the pins of merge, insertion sort, gnome sort,
cocktail and the stores-ahead-down restatement; opens recurrences on `a[k - 1]`. Needs B.

### F. Definitions at variables (`Rewrite.rewrite`)
**State:** done through the classes (`Context.defs`): the definitions of a variable are the non-variable members of its class that do not contain it, matched with the view fallback.
A variable with a non-variable definition gets the rules tried on the definition when a rule's left-hand side
has its head symbol. Ten lines. Retires the whole-atom left-hand sides. Subsumed by G, cheap now.

### G. Congruence closure, standalone (`simplify/CC.scala`)
**State:** done as `prove/Classes.scala` in the restricted form: definitions at variables plus transitivity and congruence; matching an arbitrary term modulo its class cycles (`a[k]` by `S.2[k] == a[k]`) and needs a term order or equality saturation (L).
A persistent union-find over terms with congruence propagation as a `Theory`: `assume(Eq)`, `repr` (a
non-variable definition if the class has one, a literal if it has one, else the smallest term), `members`,
`implied(Eq)`. Built and tested alone on terms; then wired into `Context` in place of `Chains.replace` and
`Chains.chain` (`↑`, `var_`, `used`, `free`, `acyclic`, the one-point rule), measured by the harness before H.
300 lines new, 150 removed, two weeks. With the joint trace, the per-variable equations of 1.3 are exactly what
the classes hold, so G and S3 meet in the middle.

### H. Arithmetic over classes (`CC` with `Poly`)
**State:** reframed: the simplex (`prove/Simplex.scala`, `Linear`) is the arithmetic; the open item is the other direction, equalities that the bounds imply merged into the classes.
Classes of integer terms carry the polynomial of their representative; linear equations solved as `Chains.solve`
does, recorded as merges, reaching function arguments through `repr`. Tests: is_sorted closes, `pr2` without
`half_even`, nested sums without `mul_eq_cancel`. One week. Needs G.

### J. Triggers and forward facts (joint)
**State:** step 1 (`{:fw}` lemmas, `Forward`) done (Oct 13, 2026): the binary search closes without the cut; step 2 (`invs` instances) open.

The bounds of a trace that a summary names (`current(incs(x0, b, ...)) <= b`) are needed as facts where only the
term occurs, e.g. at the exit of the binary search as `current(S).0`, inside other comparisons; a rewrite rule on
the atom `current(incs(...)) <= b` never fires, since the atom does not occur, and the linear constraints need the
bound as a fact to combine it with `hi <= lo` and `p <= k < q`. Triggers on inner terms, not formulas:

1. **Lemma form.** `lemma {:fw} name(...) requires C ensures φ`, the counterpart of `{:rw}`; a lemma is one or
   the other (one used both ways would rewrite its own trigger away). The trigger is the term of φ below its
   boolean, comparison and arithmetic structure that contains all variables of the lemma that the condition
   cannot bind (variables of C only are bound against the facts, as for rules); a lemma without one is an error.
2. **Firing points.** (a) When hypotheses are assumed by the traversal (the premise of an implication, the siblings
   of a conjunct or disjunct, `Simplify.assume`): their terms outside binders are matched against the triggers,
   with the matcher of the rules (`Rewrite.matches`, through definitions and views, so `current(S).0` matches
   `current(incs(...))` by its view), the conditions decided like those of rules, and the instances assumed in the
   same context, which is the right scope by construction. (b) The terms of a conclusion: the denied conclusion is
   assumed by (a) as well (`ctx.flip.assume(Nil, List(psi))` of the implication), so no separate decision-time
   firing is needed for now.
3. **The instance names the term as it occurs.** The trigger's instance is replaced by the matched term in the
   conclusion, `current(S).0 <= p`, not `current(incs(0, p, ...)) <= p`, so the fact reaches the classes and the
   linear constraints of the term the goal mentions.
4. **Generation bound.** The instances are assumed by `Context.assume`, which does not fire triggers, so facts of
   generation 1 never fire again; the static check (conclusions with no terms beyond the trigger) is not needed for
   termination then, and is kept for step 2 if a larger generation is needed.
5. **Idempotence under merges.** An instance whose conclusion is already known (`Rewrite.known`, modulo classes and
   canonical forms) is not assumed, so firing again after a merge changes nothing.
6. **Memo.** The matches per trigger and canonical term (`Canon.term`), the conditions decided per context, if the
   measurements ask for it; the views behind the matches are memoized already.

Step 2: the instantiation of an `invs` over `⌊counter(0, 1, n)⌋` at an index `j` with `0 <= j < integer(n)` when
`a[j]` or `earlier(j, xs)` is read, on the same table (trigger `earlier(j, xs)`, generation counter on the facts,
since the body brings new terms). Retires the definitional atoms, the lsearch pair, the `above_iterations_def`
interference, the cut of bsearch.

Step 3 (Oct 13, 2026, after the binary search with sortedness): fire the forward lemmas on traces where a trace is
defined (`S == trace(...)`, once per component), not at every read of `⌊S⌋.i` or `current(S).i`, and memoize the
firing per lemma and canonical term with its relevant facts. The general firing at every occurrence matches a
trace pattern through a view in every sibling context (quadratic in the conjuncts of a premise, and again in every
update), and the check whether an instance is known comes only after the match. A fixpoint of the firing over the
terms of the assumed facts (an instance enabling another at the same term) was tried for the sorted search and
works, but costs; O makes it unnecessary, and it goes with the two-layer version of the search. Firing when an atom is decided and in the contexts of
updates stays out: arithmetic facts belong in the theory (N), domain facts are assumed where the traversal assumes.

### K. Exit splitting (`Simplify.or`)
**State:** open.
The negated exit of a loop, marked by `TEQ`, distributed over the other disjuncts when a rule on their atoms
needs a literal of it. Two days. Retires the two-implication postcondition of first_duplicate.

### L. E-graph (`egraph/`, standalone library)
**State:** open; now also the home of matching modulo classes in full.
Hash-consed nodes over `Canon`, classes with a union-find, rebuilding, e-matching with pattern variables bound
to classes, extraction by size, a node budget; tested alone on arithmetic and uninterpreted terms; then binders
as nested e-graphs per combinator body; integration last as `-saturate`. With the joint trace, a loop is one
combinator and one nested e-graph, which is the case e-graphs with binders handle best. Decides whether rule
order still costs proofs after C to H; if the harness shows none, L stays a library. Two weeks for the library.

### N. Integer division by constants in the linear arithmetic (`Linear.add`)
**State:** done (Oct 13, 2026); `quot` (C's truncating division, `half_2` of SV-COMP) open: the same bounds for
`0 <= t`, a split by the sign otherwise.
`t div c` for a positive literal `c` is an opaque atom of the polynomials; whenever a constraint mentions one, the
two constraints `c * (t div c) <= t` and `t <= c * (t div c) + c - 1` are added once. A denied atom goes through the
same addition, so decisions get them as well. Decides the facts of the midpoint (`l <= (h + l) / 2` for `l <= h`,
`(h + l) / 2 < h` for `l < h`, `0 <= (h + l) / 2` for `0 <= l < h`), which retires `lemma_4` and `lemma_5` of the
binary search and about half the rewrite steps of the sorted search. Half a day.

### O. Lemmas over whole cycles: the bisection
**State:** done (Oct 13, 2026): `bsearch_bisect.dfy` in 11 s against 45 s for the two layers of
`bsearch_sorted.dfy` (both kept for now), lower_bound closes (8 s); the matcher matches traces of several
accumulators, component reads and lambdas; the repeated firing of J stays while the two-layer version is kept. As written, the guards
are higher-order in the midpoint, `G((hi + lo) / 2)`, bound by abstraction; `P` and `Q` are named by the lemma as
the cuts `cut(G, l0, h0)` and `cut((j: int) => !H(j), l0, h0)` of the guards, which rules on sortedness rewrite to the partition
points (`cut((j: int) => ar[j] < y, 0, len) == lower(ar, len, y)`), since a variable of the conclusion that only a
quantified condition mentions cannot be bound by matching. The forward instances are simplified before they are
assumed, which brings the cut to the partition point. Then (Oct 13): the trace named by a rule `bisection` with a
probe `M(lo, hi)` in place of the midpoint, any probe strictly inside the interval (`lo + (hi - lo) / 2` too); one
cut for both ends; the database module waits for the user.
The sorted binary search (`sorted(a, n)`, the array, its bound and the key as parameters) closes with the
per-component route of `incs` and `decs`, but in two layers: the reads of the array become comparisons with the
partition points `lower(a, n, x)` and `upper(a, n, x)` only for `0 <= mid < n`, which needs `0 <= lo` and `hi <= n` in
the update, i.e. the monotonicity of each component as an `invs` over its history (forward lemmas whose trigger is the
history, matched through the view), and only then do the bounded abstractions match. 48 s and 1,400 steps against 7 s
for the version with constants. The invariant is a joint one, `l0 <= lo <= P`, `Q <= hi <= h0`, and belongs in one
lemma over the trace of both accumulators, with higher-order guards and a quantified side condition decided once the
guards are instantiated (as `perm_steps`):

```
trace(l0, h0, for ⌊counter(i, c, m)⌋ do lo, hi, k ::
        case G((lo + hi) / 2) => (lo + hi) / 2 + 1, hi
        case H((lo + hi) / 2) => lo, (lo + hi) / 2)
requires l0 <= h0
requires forall j :: l0 <= j < h0 ==> (G(j) <==> j < P) && (H(j) <==> Q <= j)
gives l0 <= current(...).0 <= P, Q <= current(...).1 <= h0
```

The side condition is decided by the sortedness lemmas within the range of its premise, with no monotone layer, no
fixpoint and no forward lemma on views. How `P` and `Q` are bound (matched against `lower`, `upper` in the guards, or
named by the lemma) is to be settled when it is written. Needs patterns with several accumulators in the matcher
(S6), of which this is the first test.

### M. Diagnostics (`-probe`, budgets, timeouts)
**State:** partly done: `-debug conditions`, `-debug match` (uncovered cases, failing guards, trace patterns that fail), `-debug views`; `-probe` and budgets open.
`-probe <lemma>` reports the first failing side condition of a named rule with the facts it was matched
against and the part of a left-hand side that did not match; a separate step budget for conditions whose
exhaustion leaves the condition undecided; a timeout that reports the goal it was working on. One week.
Independent; most useful during S2 to S5.

## 3. Dependency graph and order (revised Oct 13, 2026)

```
A harness (quick)   B canonical   C lookup   F definitions   G classes (restricted)   M diagnostics (partly)   -- done
S1 to S4 the state form with views                                                                              -- done
S7 multi-accumulator core, S5 traces per SCC (done) ── J forward facts ── S6 merge and sorts, lemmas over cycles ── S8 fallback and benchmarks (deferred)
                      │
J forward facts (after S5, finishes binary search)     E the pin, K exit splitting, D renaming: pulled by S6
H equalities from the simplex into the classes: when an example needs it
L e-graph library: after S7, integrated last
```

Order after the sorted binary search (Oct 13, 2026): N (division), then O (the bisection over the cycle, with S6's
patterns of several accumulators, the sorted search as its test), then step 3 of J (firing at definitions, memo).
N and O are done (0.44.4 to 0.45.1); next: the bisection and the partition points as a module of the database (when
the user says so), the review of `{:fw}` against `{:rw}`, then S6 (the merge, a cycle of two pointers).

Order (revised Oct 13, night, S5 and S7 done for the core, Dafny and `-prove`): J, forward facts, with the exit of the
binary search as its test; then S6, the merge and the sorts in the partitioned form, which brings lemmas over whole
cycles (patterns with several accumulators) into the matcher, and E, K, D as the examples ask; the rest of S7 (the
Boogie and SMT-LIB frontends, Lean, the fallback) with S8, only when the user asks. Each step is one commit with its tests and docs (`doc/teq.md`, `doc/prove.md`), the quick
check green, and a version bump.
