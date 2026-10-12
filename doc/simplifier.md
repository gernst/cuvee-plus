# Simplifier and rewriting

The simplifier ([simplify/](../src/cuvee/simplify), `-simplify`) rewrites
formulas under the facts known at each position, with conditional rewrite
rules from the lemmas and definitions marked `:rw`. Its treatment of the
combinators of trace equation systems is described in [teq.md](teq.md), its
derivatives in [hybrid.md](hybrid.md).

## Simplification and rewriting

- [`Simplify`](../src/cuvee/simplify/Simplify.scala) rewrites assertions and
  function definitions to a fixpoint, and simplifies procedures statement by
  statement. Assertions are normalized into clauses (`Normalize`) before
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
    applies. An assertion that remains carries the counts as attributes
    `:used (name count)`, which a later `-simplify`, e.g. after `-split`, adds
    to; one that simplifies to true is reported on stderr with them, by its
    `:named` or as `goal n` (`used by goal 1, which simplified to true: ...`,
    not starting with `goal`, which would be taken for a remaining goal). Applications in subterms that are dropped later
    count as well, so that the counts are an upper bound
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
  - Statements have helpers likewise, `spec`, `assign`, `block`, `choice`,
    `if_`, `while_`, ...: statements without effect are the empty block
    `skip`, `block` merges nested blocks (hoisting locals unless they
    capture), drops `skip`, statements after a jump, and unused locals, and
    `if_` reduces constant tests, equal branches, and negated tests.
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
    `0, ..., k - 1` is that polynomial. The difference constraints bound every
    remainder by `0 <= e % k <= |k| - 1` (`Diffs.ranges`). The update of a
    trace whose results are remainders modulo `k` or the accumulator, and
    whose initial value is in the range, assumes the range of the accumulator
    (`wrapped`), which holds for all its values by induction, such that the
    remainders under the test of the loop are dropped
    ([remainders.dfy](../examples/dafny/simplify/remainders.dfy),
    `examples/c/teq/unsigned_*.c`).
  - Derivatives are computed by the rules of dL ([hybrid.md](hybrid.md)).
- [`Rewrite`](../src/cuvee/simplify/Rewrite.scala) applies conditional rules
  innermost first, also as a library. Its methods take
  `(config, state, ctx, ...)` as well; matches are substitutions, and side
  conditions are decided by `Simplify.simplify` in the context. Matching
  below the combinators of TEQs is described in [teq.md](teq.md).

## Data structures

- **`Context`** is a sequent at the current position:
  - three theories (`Theory`: immutable facts that detect inconsistency), to
    which `assume` and `deny` pass each fact: the assumptions and conclusions
    as given (`Facts`), the equations of variables (`Chains`), and the
    difference constraints on `Int`, closed by incremental Floyd-Warshall
    (`Diffs`), whose negative cycles make the context inconsistent;
  - bound variables;
  - in `Chains`, equations of variables with variables or literals, as a map
    `replace`, which the simplifier substitutes eagerly (`var_`);
  - in `Chains`, the solutions of arithmetic equations for a variable
    (`solve`), e.g. `x` by `40 - n` for `n + x == 40`, as a map `solved`,
    which `poly` inlines into polynomials, unless the solution depends on the
    variable through the equations of the context (`acyclic`), e.g. `n` by an
    expression over a trace `K` with `K == counter(0, 1, n)`, which would
    loop; the equation remains an assumption;
  - in `Chains`, the non-recursive equations `x == e` among the assumptions whose `e` is
    not an arithmetic operation (`+`, `-`, `*`), as a map `chain` from variables
    to expressions (the equation remains an assumption), also if they depend
    on each other, e.g. of mutually dependent traces, since the chain is looked
    up one variable at a time; the variables are not
    substituted, but the extractor `ctx.↑(e)` sees a variable as its
    definition if that is not a variable, and does not match it otherwise,
    and any other expression as itself, by which rewriting matches a variable
    inside of the expression like its `e` (`Rewrite.matches`), and the helpers
    of the simplifier look through definitions, e.g. read over write of
    `a == b[i := v]`, beta reduction of `a == (λx. e)` in `a[t]`,
    testers of `xs == cons(x, ys)`, counters
    `K == counter(0, 1, n)` among the dependencies, and equal definitions in
    `eq_`; a variable is never rewritten on its own;
  - the bound variables in the order of binding (`bound`), and among them
    those that are universal and existential at the current position
    (`universal`, `existential`, added by `forall` and `exists`, while `bind`
    adds to neither), which `flip` swaps; the equations of the
    existential ones are true (the one-point rule);
  - the polarity of the position, and whether the context is inconsistent;
  - the rewrite rules and their remaining number of steps
    (`ctx.withRules(rules, steps)`), which all copies share; `Context.assume`
    adds an equation `l == r` of the assumptions with a ground `r` as a rule
    without variables (`Context.rule`), if `l` has free variables and is neither a
    variable nor an application of an arithmetic operator. The rules terminate,
    since each step removes occurrences of variables.
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
- **`Constraint(poly, strict)`** is a linear constraint `0 <= poly` or
  `0 < poly`. `FourierMotzkin` eliminates atoms from conjunctions of these and
  decides their satisfiability over the rationals.
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
  over `⌊X⌋` (`self` of `Rewrite.matches`), e.g. the test of a loop.
  A function definition with `:rw` whose body is a match on a parameter
  gives one rule per case, the pattern in place of the parameter, and
  the other parameters that clash with pattern variables renamed apart
  (`Rule.from(state, fun, body)`). Overlapping patterns are not handled: a later
  case's rule also fires on arguments that an earlier case matches.

## Fusion

- **`Fuse(state, g, f)`** fuses the composition `g(f(xs), ys)` of two `Rec`s
  into one `h(xs, ys)` (fixpoint fusion, deforestation): one case per case of
  `f`, whose body `e` becomes `g(e, ys)` with `g` driven into it. A recursive
  call of `f` becomes one of `h`, conditionals are driven into their branches,
  and a constructor application selects the cases of `g` statically in their
  order, with their guards as tests (`Ite`). Inside the selected bodies,
  `g(f(t), z)` becomes `h(t, z)`. If a pattern is undecided, i.e. it has a
  constructor where the expression has none, `g` is applied as a value
  (`Apply`), as are the remaining calls of `g` and `f`. The result is equivalent if
  both are total and their recursion is monomorphic.

## Forward reasoning

`Simplify` and `Rewrite` reason backwards from the goal. A subterm of the goal
is rewritten when the left-hand side of a rule matches it and the rule's
condition holds in the context. The context is consulted for decisions
(`Context.implied`, `Context.denied`, `Rewrite.holds`), and since side
conditions bind variables, also for matching (`Rewrite.conditions`). New facts
are not derived from it.

Some goals hold only because of facts that the goal does not mention, e.g. in
the not-found exit of binary search (see
[binary-search.md](../ideas/binary-search.md)), the bounds of the probes, or
`lastlt < k` and `k < lastgt` for the index `k` of `x` in a sorted array,
whose lemmas never fire, since their conclusions are not subterms of the goal.

Matching suffices to derive them, no unification is needed. The facts of the
context are ground with respect to the lemmas, since the variables of the goal
are moved into the context by `Split` and `Simplify` and act as constants. To
apply a lemma `if P₁ && ... && Pₙ then C`:
1. match `P₁` against a fact;
2. match `P₂` under the resulting substitution, and so on;
3. backtrack over the choices.

This is the instantiation of quantifiers by triggers in SMT solvers
(E-matching), with `Rewrite.matches` for each premise. Unification would be
needed only to combine lemmas with each other (resolution, superposition).

Two designs:

- **Option A, conditions that bind variables (backward):** variables of a side
  condition that do not occur in the left-hand side are bound by matching the
  condition against the facts, e.g. `k` of `a[k] == x`, and the lemma states
  its conclusion in the shape of the goal. This is implemented on `main`
  (`Rewrite.conditions`, see `Rule` above). Its limitation is that derived
  facts are not combined: the lemma must state `lastlt + 1 < lastgt`, not the
  two facts `lastlt < k` and `k < lastgt`.
- **Option B, forward rules (saturation):** lemmas with an attribute `:fw`
  are applied when `Context.assume` records facts. Their premises are matched
  against the facts, their conclusions simplified and assumed, and the
  context combines them, e.g. by its difference constraints (`Diffs`). This
  gives:
  - general lemmas on sortedness;
  - facts about terms that occur, e.g. the bounds `x0 <= current(X)` of a
    monotonic trace from its equation `X == trace(...)`;
  - the instantiation of `invs` and quantified hypotheses at the terms that
    occur, e.g. `if invs(for xs check v :: P(v)) && 0 <= j < |xs| then P(earlier(j, xs))`,
    triggered by `earlier(j, xs)`.

  Guards against blow-up: every variable of a conclusion is bound by the
  premises (`Rule.checkForward`); the conclusions are derived one level deep,
  without forward rules of their own.

  Option B is implemented on the branch `forward`. There, the first premise
  is the trigger, matched against the new facts of `Context.assume` only, and
  the siblings of conjunctions are recorded without forward rules. Its notes
  describe an open question: how conclusions reach sibling hypotheses, e.g.
  the invariants of a trace equation in the updates of another one.

Without forward rules, cuts state such facts in the program,
`assert φ; assume φ;` after a loop, where the assertion is a goal whose atoms
the rewrite rules apply to (see
[bsearch.dfy](../examples/dafny/teq/bsearch.dfy)).
The SV-COMP examples instead abstract an iteration constraint by an atom,
which a second lemma takes as its side condition (see
[summary.md](../benchmarks/sv-comp/dafny/summary.md)); the lemma database does
the same, since an iteration constraint as a side condition recurs through the
facts it is matched against (see [teq.md](teq.md)).
