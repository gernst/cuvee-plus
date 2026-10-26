# Consolidating the engine of `-prove`

A review of src/cuvee/prove (Oct 26, 2026; 4712 lines, 2290 of them in Simplify and Rewrite) after the work on the
normal forms (ideas/engine-gaps.md, steps 3 and 3b): most problems of that work were at the seams between mechanisms
that do the same thing in different places. The proposals below unify them; each names the places that overlap now.
TODO.md ("Code structure") lists some of them already; they are repeated here where they belong to a unification.

## 1. Where values enter terms (normal forms) (done in part, 0.52.12)

Done: the operations `Classes.term` (how a variable is written), `value` (a leaf of arithmetic with its solution),
`fixed` (a variable with a literal value) and `fact` (the canonical form of a fact) are the only ones by which
`Simplify`, `Context` and `Rewrite` use the policy; `rank`, `normalize`, `substitute` and `acyclic` stay inside
`Classes`.

Now: the canonical form of a term is decided in five places, by different policies.
- `Classes.normalize`: facts, by the roots of their classes and the solutions inside arithmetic;
- `Simplify.var_`: every variable of a term by the root of its class, literals included;
- `Simplify.poly`, `arith`: arithmetic with the solutions of `Classes.substitute`;
- `Canon.term`: terms with binders, for keys and comparisons only;
- `Context.fix`, `Classes.rank`, `Classes.acyclic`: which value a variable has, which member is a root, which
  solution may be used.

The experiments showed that these are one decision spread over five files: the order of roots in `Classes.rank`
changed what `var_` writes, which broke `fix` (a literal root as the test for "fixed") and `normalize` (a literal
replaced by its root, the cycle of benchmark43).

Proposal: one object for the policy, used by the classes, the simplifier and the facts, with three operations: the
canonical variable of a variable, the value of a variable inside arithmetic (literal or solution), and the canonical
form of a fact. The order of roots, the acyclicity of solutions and the test "has a value" live there and nowhere
else. Then a change such as "variables before literals in terms" is a change of one operation, not of five places.

## 2. One view of arithmetic (done in part, 0.52.13)

Done: `Arith.difference`, the difference of the sides of a comparison as a normalized polynomial with an offset and a
function for the leaves, the one conversion of comparisons used by `Simplify.difference` (leaves simplified in the
context, primitive) and `Rewrite.comparison` (without context, `<` on Int as `<=` of the successor). The matcher's
signed summands stay: they take apart the expression as it is, which a polynomial would reorder.

Now: polynomials are built and taken apart in four places.
- `Arith`/`Poly`: the normal form;
- `Simplify.difference`, `lt`, `le`, `eq`: comparisons via `Poly.sides`, `floor`, `primitive`;
- `Rewrite.comparison`, `signed`, `summands`, `negate`, `sum`, `product`, `factors`: the matcher's own view of sums and
  products as signed lists of expressions;
- `Linear`: rows of the simplex.

Proposal: the matcher works on `Poly` (its summands are the monomials with their factors), `Rewrite.sum`/`product`
become `Poly.toExpr`; the comparisons of `Simplify` and the constraints of `Linear` share one conversion of an atom of
comparison to a polynomial (`p <= 0`, `p < 0`, `p == 0`). `Arith.normalize` is unused (TODO.md).

## 3. One decision procedure (done in part, 0.52.12)

Done: `Simplify.decide`, the decision by the theories as one `Option[Boolean]`, used by the main loop. Correction of
the review: the side conditions are decided differently on purpose, by simplification with the rules
(`Rewrite.holds`) and by lookup among the facts (`Rewrite.known`); a cache is still open.

Now: whether two terms are equal or a formula holds is asked in several ways.
- `Simplify.eq_` (syntactic, `ctx.↑` definitions, classes, `Canon.equal`, `point`, literals, extensionality);
- `Simplify.implied`/`denied` (simplify, then `True`) and `Context.implied`/`denied` (deny and check the theories);
- `Classes.equal`, `Classes.within`, `Canon.equal`;
- `Rewrite.known`, `shaped`, `holds`: side conditions looked up among the facts modulo classes and canonical forms.

Proposal: `ctx.decide(phi): Option[Boolean]` with a fixed order of cheap to expensive checks (syntactic, the classes,
the canonical forms of binders, the facts, the simplex) and a cache per context; `eq_`, `holds`, `known` and the
decisions of the helpers (`select`, `distinct`, guards) call it. Today the same pair is often decided several times
on one path, without a cache (TODO.md: guard decisions are repeated without a cache).

## 4. One mechanism for facts derived on assumption (done in part, 0.52.13)

Done: the instances of a forward lemma at a term are memoized by the lemma, the term and the canonical facts of the
context (`Forward.fire`, `Context.memo`), so an instance is simplified once per context, not at every firing; the
counts of `-rules` include the rules used inside a memoized instance once. Kept by decision: the forward lemmas fire
at the positions where the simplifier assumes facts (premises, siblings of `and`/`or`, the facts of `Slice`), not in
every `Context.assume` (contexts of combinators, cases, branches), which would add instances; moving them into the
context would need the simplifier there (step 6) and changes nothing else, since the rules from ground equations and
the values fixed by the simplex are derived in `Context.assume` already.

Now: assuming a fact derives further facts in three ways.
- `Context.rules`: an equation of a term with a ground term becomes a rewrite rule;
- `Forward.assume`/`saturate` (and `Simplify.forward` at decided comparisons): instances of forward lemmas, simplified
  at every firing (TODO.md, the cost of `-prove`);
- `Context.fix`: a variable fixed by the simplex becomes an equation with its value.

Proposal: one saturation step of `Context.assume`, with the derived facts of all three kinds, one generation bound and
one memo of instances by the canonical form of the fact (`Canon.key`), so that an instance is simplified once per
context, not at every firing.

## 5. Alternatives of a term in matching (done, 0.52.13)

Done: `Rewrite.alternatives`, the groups of terms a pattern may match instead of a term (the definitions, the
structural view, the projected view), computed lazily and tried in order by `matchesExpr`.

Now: when a pattern does not match a term, `Rewrite.matchesExpr` tries, in a fixed chain, the definitions of a
variable (`Context.defs`), the structural view of a component (`Views.structural`), and the projected view
(`Views.projected`); `Forward` matches its triggers the same way, and `Rewrite.combinator`, `component` and
`matchesCases` have their own fallbacks.

Proposal: `ctx.alternatives(term)`, a lazy sequence of the terms that a pattern may match instead of `term` (its class
members, its views, later its canonical arithmetic form), used by the matcher, the triggers and the conditions; the
debug output of failed matches (`-debug match`) then reports per alternative.

## 6. Matchers as objects (not done, by decision)

The parameters stay: the gain of a `Simplifier` and a `Matcher` class does not outweigh a diff over all of Simplify
and Rewrite.

Now: `matchesExpr`, `matchesExpr_`, `matchesExprs`, `matchesSummands`, `matchesFactors`, `matchesCases`,
`combinator`, `component`, `arguments`, `abstraction`, `instantiate`, `guard`, `conditions` take 12 to 15 parameters
each (`config, state, ctx, params, vars, locals, pat, self, bound, avoid, arg, subst`), most of them unchanged
along a match (TODO.md).

Proposal: a class `Matcher(config, state, ctx, rule)` with the fixed parameters as fields; the methods take the pattern,
the term, the bound variables of the expression and the substitution. The same for the simplifier, a class
`Simplifier(config, state)` instead of threading both through 61 methods (TODO.md).

## 7. Memos (done, 0.52.13)

Done: `Context.memo(kind, deps, bound)(compute)`, one table for the facts of combinator contexts, the reads of their
iterations and the instances of forward lemmas; the views keep their own key (the facts that mention their
variables).

Now: the context keeps several memos keyed by `Canon.key` with the renaming of bound variables back and forth
(`Context.memos`: combinators, reads, views; `Canon.back(re)` at every lookup), each with its own key construction
(`Simplify.combinator`, `Simplify.iterations`, `Views.projected`).

Proposal: one `Memo[V]` in the context, `memo.get(ctx, bound, extra)(compute)`, which builds the canonical key and
renames the value back; the three users pass only what they compute.

## 8. Choices and cases (not done, by decision)

`Split` and `Normalize` do different things; the places below stay as they are.

Now: guarded cases are built, lifted, merged and split in six places.
- `TEQ.update`: the cases of the paths of a loop body (grouped by their results since the worktree of Oct 26);
- `Simplify.eps`: merged by equal results after simplification, flattened;
- `Simplify.cases`: conditionals of the results of traces lifted into cases;
- `Normalize.lift`, `ite`, `replace`: conditionals lifted out of atoms into formulas;
- `Prove.cases`, `alternatives`: case splits of remaining goals;
- `Split` (transform), `Normalize.flatten`, `Context.assume`: the decomposition of sequents (TODO.md: three times).

Proposal: one module for choices with the operations build (from paths or conditionals), group (by results, modulo a
directed test later, ideas/engine-gaps.md), lift (out of terms and atoms) and split (a goal by cases), and one
decomposition of sequents used by `Split`, `Normalize` and the context; `ideas/dnf-guards.md` would change only this
module.

## 9. Small duplications and names (done, 0.52.12, except `Context.not`)

Done: one `Normalize.replace` with a parameter `binders`; `Rewrite.counter(ctx, dep)` returning the bound of the
counter of the iterations, used by `Rewrite` and `Simplify.iterations` (the test occurred twice, not five times;
`Simplify.deps` tests for any counter); the lifting of conditionals is `Simplify.choices`.

- `Normalize.replace` and `Forward.replace` replace a subterm, the first not below binders, the second everywhere;
  one function with that choice as a parameter.
- `Rewrite.iterations(ctx, dep)` (is a dependency the counter of the iterations) and `Simplify.iterations` (the facts
  of a combinator context) share a name; the test for the counter `Butlast(ctx.↑(Counter(0, 1, _)))` occurs in
  `Rewrite.iterations`, `Simplify.iterations`, `Simplify.deps` and twice more (TODO.md: extracted three times): one
  helper `ctx.counter(dep): Option[Expr]` returning `n`.
- `Simplify.cases` exists twice (cases of a `match`, and the lifting of conditionals into choices since 0.52.7);
  `Context.not` and `Simplify.not` (TODO.md).

## Order

Done: 1, 2, 3, 4, 5, 7, 9 (in part where noted); not done by decision: 6, 8.

The original order: 1 and 3 first: they are where the experiments of Oct 26 failed, and they make the redesign of ideas/engine-gaps.md
(3b) a change of one place. Then 4 (the cost of forward lemmas), 5 and 6 (they simplify each other), 8 together with
the DNF guards, 2, 7 and 9 as cleanup. Each step is a refactoring without a change of results: the examples, the test
suite and one cloud run of Arrays and Loops must not change.
