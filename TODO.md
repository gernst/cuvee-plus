# TODO

Open problems, limitations, and inconsistencies, grouped by area; the
architecture is described in [doc/architecture.md](doc/architecture.md).

## New

- support verifying trace lemmas in Dafny
- identify performance improvements, notably in the simplifier
- thread config through more code, so that it is usually available
- error messages should use a nice printer
- C frontend: `goto` to a label whose statement falls through, by copying
  the statements

## Bugs

- A bound variable may capture a constant of the same name in the output of
  SMT-LIB: normalization renames bound variables apart from free variables,
  but constants (`declare-const x`) are functions, e.g.
  `(=> (exists ((x Int)) (< x y)) (<= x y))` becomes
  `(forall ((x Int)) (=> (< x y) (<= x y)))` with `-simplify`.
- A rule whose left-hand side is a comparison of two open variables, e.g.
  `j < n` with a side condition `invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: P(k, h))`,
  overflows the stack before any step: it matches every comparison, also
  the bounds `0 <= k < n` of the iterations that matching the `invs` of the
  side condition assumes in the context of its body (`Simplify.combinator`),
  where the rule is tried again (see
  [standard_find_ground-1.dfy](examples/sv-comp/array-examples/standard_find_ground-1.dfy)).
- A side condition that is an equation between applications with a variable
  that is not instantiated yet, e.g. `prefix(n, xs) == prefix(n, ys)` with `n`
  open, is not matched against an equal hypothesis
  `prefix(N, t) == prefix(N, u)`, while `q(prefix(n, xs), prefix(n, ys))` and
  `xs == ys` are; reproduced with `-simplify` alone on a lemma
  `if prefix(n, xs) == prefix(n, ys) then (earlier(j, xs) == earlier(j, ys)) <==> true`
  (see [standard_compare_ground.dfy](examples/sv-comp/array-examples/standard_compare_ground.dfy),
  which uses the predicate `agree` instead).
- A pattern with two cases matches an update with a single case, which one
  case of the pattern covers (`Rewrite.matchesUpdates`); variables of the rule
  that occur only in the other case stay uninstantiated, and the rule is
  applied anyway: the lemma
  `trace(x0, ... :: case c => F(x, k, h) case !c => G(x, k, h)) == if c then trace(... F ...) else trace(... G ...)`
  rewrites `trace(a, ... :: x[h := x[h] + 2])` to
  `if true then trace(... F ...) else trace(... G ...)` with `G` free, which
  does not terminate (see [condm.dfy](examples/sv-comp/array-fpi/condm.dfy)).
  This is why the joins of guarded stores are not part of teq.dfy: they
  match every store with one case, e.g. `a[k := a[-k + 99999]]` of
  [standard_palindrome_ground.dfy](examples/sv-comp/array-examples/standard_palindrome_ground.dfy),
  as `if true then ... else G(a, k, h)` with `G` free, which hides the update
  from other lemmas.
- A sum that contains a bound variable of a combinator in a pattern is not
  matched, even against the same sum: the lemma
  `current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: a[k := a[k + -1]])) == hit(a0)`
  does not rewrite `current(trace(a2, for ⌊counter(0, 1, N)⌋ do a, k :: a[k := a[k + -1]]))`
  with `-simplify`, while `a[k := a[k] + d]` matches `a[k := a[k] + 6]`;
  recurrences over the previous element are not matched (see
  [ifcomp.dfy](examples/sv-comp/array-fpi/ifcomp.dfy)), only those whose
  index is a dependency, e.g. `⌊counter(1, 1, n)⌋` (see
  [eqn1.dfy](examples/sv-comp/array-fpi/eqn1.dfy)).
- A cycle through the arithmetic: in [ss1.dfy](examples/sv-comp/array-fpi/ss1.dfy), the equation
  `sum₄₀ == sum₂₂ + sum(selects(a₃₁, ⌊I₃₉⌋))` is solved for `sum₂₂` (`Chains`), whose value is then inlined into
  `⌊consts(n, sum₂₂ + 1)⌋`, which `selects_stores` returns for `selects(a₃₁, ⌊I₃₉⌋)`, which reappears in the
  solution; the poly guard against cycles (`Simplify.poly`) sees the equations of the context only, not the rules.
  Remedies: prefer to solve for the variable that occurs in fewer definitions (`sum₄₀`), or reject a rewrite whose
  result contains the rewritten term (`Rewrite.apply`). Also non-terminating, not analysed yet:
  [add-3-n-u](examples/sv-comp/array-multidimensional/add-3-n-u.dfy), `copy-partial-3-u`, `diff-3-n-u`.
- A cycle through a side condition: `sum_invs_const` of teq.dfy has the left-hand side `sum(js)`, which matches
  every sum, and the side condition `invs(for ⌊counter(0, 1, n)⌋, js check k, j :: j == c)`, open in `n` and `c`,
  which `Rewrite.conditions` simplifies before it searches the facts. For `js` a term like
  `prefix(natural(k), maps(...))`, that builds the contexts of combinators with their iterations, whose reads of
  the dependencies produce new sums, on which `sum_invs_const` is tried again, until the budget is exhausted; e.g.
  [ps2-ll.dfy](examples/sv-comp/nla-digbench/ps2-ll.dfy) repeats the same reads about 117 times and terminates
  after 48 steps without the lemma; likewise ps3-ll to ps6-ll, cohencu-ll, cohendiv-ll, for_bounded_loop1,
  copy-3-n-u, diff-2-n-u (13 of the 16 errors of the Dafny translations at 0.34.22). Remedies:
  1. A reentrance guard for conditional rules: while the side condition of a rule is decided, the rule is not
     applied inside, e.g. a set of such rules in the context that `Rewrite.apply` skips; this cuts the recursion
     for all conditional rules, and loses only side conditions that need the same rule again.
  2. Open side conditions that contain combinators are only substituted, not simplified, before they are searched
     among the facts, which are simplified already; simplification is needed for normalization elsewhere, e.g.
     beta reduction after a higher-order match, hence only for combinators.
  3. A separate budget for side conditions, whose exhaustion leaves the condition undecided, such that the rule
     does not apply instead of aborting the command: a safety net, which turns errors into open goals.

  Not remedies, measured on the Dafny translations: stating the lemma as the definition
  `invs(... j == c) <==> js == ⌊consts(n, c)⌋` rewrites the `invs` facts that `Simplify.invariants` uses
  pointwise; recording the counters that the context iterates over and not injecting their invariants again
  (`Context.iterating`) ends bresenham-ll only; not renaming the bound variables of combinators, with binders
  that shadow those of the context (`Context.bind` hiding the facts about them), makes the terms stable across
  rounds, but the repetitions above remain, and it closes nothing (241 against 243 true, within the noise).
  The injection of 7b420a0, all invariants over the counter of a loop pointwise with `earlier(natural(k), Z)`, made
  the nested reads recurse further (19 errors), and is reverted in 0.34.23.
- [sanfoundry_02_ground.dfy](examples/sv-comp/array-examples/sanfoundry_02_ground.dfy) times out (60 s), on the trace
  of the two largest elements, whose updates read the array at the counter from 2.
- `-teq` overflows the stack (an uncaught `StackOverflowError` in `Subst`) on
  a loop body with ten conditionals in sequence, presumably from the 2^10
  paths of its symbolic execution (see
  [diamond_2-2.dfy](examples/sv-comp/loop-acceleration/diamond_2-2.dfy)).

## General

- Function types (`arrow₁`, ...) and their applications (`apply₁`, ...)
  are printed and parsed in SMT-LIB as those of SMT-LIB 2.7, `(-> A B C)`
  and `(@ f a b)`; they are marked `{:ho}` and their declarations are not
  passed to solvers, which hardly support them.
  Lambdas of SMT-LIB are arrays of a single variable, since solvers support
  only those, hence lambdas of function type printed in SMT-LIB are not read
  back.
- The implementations of overloaded operators that are not part of cvc5
  (`seq.store`, `seq.member`, `seq.proper_prefixof`, `set.proper_subset`,
  `bag.select`, `bag.proper_subbag`, `map.store`, see `core.Overload`) are
  declared in the SMT-LIB prelude, but not defined, so the solvers reject
  them; definitions in terms of cvc5's functions are to be added, e.g. in
  the Dafny prelude. Until then, `examples/dafny/vcgen/seq.dfy` is not
  verified (`Examples.unsupported`), and the cvc5 tests of `seq.dfy`,
  `sets.dfy`, and `invalid_sets.dfy` are removed.
- Goals that do not hold are reported by the solver sink with their formula
  in SMT-LIB, not in the language of the input like the other reports.
- An input file with an unknown extension, e.g. a preprocessed C file
  `.i`, ends in an uncaught exception with a stack trace
  ("unsupported command line option or input file"), since `Config.parse`
  raises outside of the pipeline; the task definitions (`.yml`) of such
  files are read.
- Readers of input files and the stream of `-o` are never closed.
- `Match`: parsed only in Dafny (expressions, without case conditions, not
  statements), printed in Dafny and SMT-LIB without case conditions; the
  simplifier does not reduce it on constructors (only `Fuse` selects cases),
  no rewriting modulo matches.
- Tests that run z3 have its default timeout of 1 s per query, which a
  loaded machine may exceed: `c.Translation.increments in expressions` failed
  with `unknown` while z3 unrolled a loop with the constant bound 10 (about
  0.17 s alone); with a symbolic bound it finds a linear invariant (0.035 s).

## Dependencies of equal length

The combinators assume that their dependencies have equal lengths (an invariant of the core, see
`Type.dependencies`), which teq.dfy never states: e.g. `current_stores` holds only if `|keys| == |values|`, and
`current_trace_flag` only if `|hs| == n` for the dependency `⌊counter(0, 1, n)⌋`. In Lean, the dependencies are
zipped, which truncates to the shortest one, so such lemmas are false without the assumption.

Plan:

1. Make the invariant part of the semantics: a term is well-formed if the dependencies of each combinator in it,
   also in the definitions of the functions of teq.dfy (`stores(a, keys, values)` is a trace over `keys, values`),
   have equal lengths. The lemma database is sound for well-formed terms only, which is all that -teq builds: the
   dependencies of a loop are `⌊X⌋` of its traces, which all have `n` steps.
2. Rewriting preserves the invariant if each lemma maps well-formed left-hand sides to well-formed right-hand
   sides, e.g. `prefix_stores` cuts `keys` and `values` to the same length. This is a proof obligation of each
   lemma, not a check at run time.
3. In Lean, each lemma gets the hypotheses that the combinators of its left-hand side are well-formed:
   `d₁.length = d₂.length` for the dependencies, with the lengths of `butlast (counter i c n)` and of the other
   functions given by lemmas (the length of `butlast (counter ...)`, of `maps` and of `butlast (trace ...)`),
   stated by hand in teq.lean; a lemma about the right-hand side (well-formedness) is proved along with it.
4. Lemmas whose assumptions cannot be derived from well-formedness (`earlier_consts` outside the trace,
   `prefix_prefix` for `j > k`) get `requires`, which makes them conditional rules; check on the SV-COMP
   database that the simplifier still discharges them in the contexts of the goals.
5. Document the invariant and the soundness of the database modulo it in doc/teq.md.

## Proofs of teq.dfy in Lean

- [teq.lean](resources/cuvee/teq.lean) is maintained by hand next to teq.dfy, without a generator: a changed lemma of
  teq.dfy is changed there too. Of its lemmas, most are proved; the others are `sorry` and fall into three groups,
  with counterexamples at the end of the file where they are refutable: they hold only for dependencies of equal
  length (see above, e.g. `sum_add`, `count_false_true`, `agree_prefix_def`, `current_trace_cap`), only for indices
  within the lists, whose elements are `unspecified` otherwise (`earlier_counter`, `earlier_sums`,
  `current_stores`, `prefix_counter` for `k > n`), or only for complete guards, which the conditionals of the
  updates in Lean lose (`current_trace_bounded`). `invs_two_phases` holds but is not proved yet.
- The Lean check takes about 6 s, mostly `simp` and typeclass inference for the decidability of `if` on generic
  types under `open Classical`; `simp only` instead of `simp` would speed it up.

## Printers

- The Lean printer (`-print lean`) prints no preamble: the output needs
  `open Classical` and Mathlib (`ℝ`, `Set`), and names of the input that
  Lean declares already clash, e.g. a datatype `List` or a function `max`,
  which a namespace around the output would avoid. Not checked with Lean.

## Code structure

Opportunities for cleaning up, making the code uniform, and merging common
concepts, found by reading the whole code base; none is a bug.

### Core

- One generic traversal with binders: `Subst.apply`, `Old.instance`,
  `Type.expand(expr)` and `Rec.calls` each repeat the list of binders
  (`Bind`, `Lam`, `Trace`, `Maps`, `Invs`, `Let`, `Match`, `Rec`); the `Match`
  and `Rec` loops of `Old.instance` are the same. `Type.numerals` uses
  `expr.map` for its side effect, which a fold over the children would serve.
  `Type.expand(prog)` repeats the cases of `Prog.map`.
- Numeric sorts: Int and Real are twins in `Fun.int`/`Fun.real`, in
  `Builtin` (`Ints` and `Reals`), in `Overload.int`/`Overload.real`, and in
  their rings `Ints.ring` and `Reals.ring`.
  - `isSum`, `isArith` and `isComparison` enumerate the functions by hand.
  - `Ring` lacks `lt`, `le` and `div`, hence `Simplify.once` (`Eq`, `Lt`, `Le`,
    `Gt`, `Ge`, `not`, `diff`), `Rewrite.comparison`, `Diffs` and the
    printers spell out both sorts.
  - `Ints` and `Reals` are the objects per numeric sort with the sugar,
    literals, and ring; `Ring` could take their comparisons as well.
- Builders of applications: `Overload.app` binds types without expanding,
  `App.apply(state, ...)` expands, `State.exprs.app` instantiates fresh type
  parameters, and `smtlib.Parser.app` does the same again. Two builders with
  clear roles would do.
- Sugar: `Seqs`, `Sets`, `Bags` and `FinMaps.empty` are copies
  (→ `Sugar.empty`). `Sugar.unary/binary/ternary` are one class for three
  arities. `associative` and `commutative` overlap in `flatten`. The `all`
  lists of `Fun.seq`, `set`, ... are written by hand.
- `Rec.from` and `Rule.from(state, fun, body)` both turn a definition that
  matches on a formal into cases. `Rule.from` does not substitute the pattern
  for the formal; it could use `Rec.from`. `Rule.from` accumulates premises
  with `if cond == True then ... else And(...)`.
- `Subst.apply(attrs)` maps expressions only, so `modifies` lists are neither
  renamed nor retyped, while `Type.expand(attrs)` handles them
  (→ `Attrs.map` with a function for variables).
- `State` keeps a declaration, attribute and definition map per kind (sorts,
  functions, variables, procedures). Each repeats the checks "already
  declared" and "not declared" (→ one generic table). `exprs.trace`, `map`
  and `all` repeat the creation of the bound variables.
- `history`: `State.history` exists, but `Prog.Par`, `Type.check(Ode)` and
  `Verify.tick` look up `state.vars.get("history")`.
- `Type`:
  - `unify` and `bind` repeat the unfolding of defined sorts;
  - `Error.report("type mismatch", ...): unify(...)` occurs about ten times;
  - the checks of `Match` and `Rec` repeat those of the cases;
  - the comment above `BitVec` belongs to `object Param`.
- The ordering of expressions is by `toString` (a TODO in `Expr`).
- `Justify` is mapped to its keyword in four places:
  `smtlib.Parser.justification`, `smtlib.Printer.command`,
  `dafny.Printer.format` and `boogie.Printer.format`.
- `Attrs(attrs.map(_ -> None))` for flag attributes occurs six times in the
  Dafny parser (→ `Attrs.flags`).

### Simplifier

- `Simplify`, `Rewrite` and `Fuse` thread `(config, state, ctx)` through
  every method (→ a class `Simplifier(config, state)`). Programs are
  simplified without context, yet `ctx` is passed.
- The matching functions of `Rewrite` take 12 to 15 parameters.
  - `config`, `state`, `ctx`, `params` and `vars` are fixed per rule; `locals`,
    `self`, `bound` and `avoid` change below combinators
    (→ a matcher object per rule and a record for the binding).
  - The three combinator cases repeat the construction of the inner context.
- Matchers:
  - three on types: `Type.bind`, `Type.unify` and the one-sided
    `Rewrite.matches` on types;
  - two on constructor patterns: `Rewrite` and `Fuse.matches` (`Outcome`).
  - The simplifier does not select the cases of a `Match` on constructors.
- `Subst.rename(bound, ctx.free)` followed by `ctx.bind`/`forall`/`exists`
  and the renaming of the body occurs about ten times
  (→ `Context.enter(bound)`).
- `Simplify.integers`, which turns the bound naturals that occur only as
  `integer(n)` into integers within their range, is clumsy: a filter, a map
  for the new variables, a substitution as a map, and a fold for the
  replacement, with `asInteger` and `integer` as two traversals that collect
  by side effect and rebuild by `Expr.map`; it runs on every quantifier
  before the body is simplified, and the cases `All` and `Ex` repeat the
  wrapping of the ranges (→ one traversal that collects the occurrences and a
  `Subst` for the replacement, or a rewrite of `integer(n)` when entering the
  binder via `Context.enter`, see above).
- The counter of the iterations, `Butlast(ctx.↑(Counter(Zero, One, n)))`, is
  extracted in `Rewrite.iterations`, `Simplify.iterations` and
  `Simplify.deps` (→ one extractor).
- In `Simplify.once`, `Eq(x, Trace(...))` repeats the case `Trace(...)` and
  `Eq(y, Maps(...))` the case `Maps(...)`.
- Polynomials:
  - `Arith.toPoly` and `Simplify.poly` are the same descent;
  - `Rewrite.comparison` recomputes `Simplify.difference`;
  - `Rewrite.signed`, `summands`, `negate` and `sum` belong in `Poly`;
  - `Arith.normalize` is unused.
- Sequent decomposition along the connectives is done three times:
  `Split.assert/assume` (obligations), `Normalize.flatten` (one clause) and
  `Context.assume(pos, neg)` (facts). `Split.avoid` equals `Normalize.avoid`.
- Naming and leftovers:
  - `Context.not` (double negation) and `Simplify.not` (normal form) have the
    same name but different contracts;
  - `Simplify.show(expr)` and `show(rule)` duplicate the one-line rendering;
  - `Rewrite.unmatched` is an alias of `Nil`;
  - commented-out code in `Rewrite.apply`;
  - trailing spaces in `Simplify.arith`.
- `FourierMotzkin` is used only by its test (see below).

### Transforms and verification

- `Verify`, `TEQ` and `Horn` repeat the setup of a procedure (→ one helper):
  - the contract and the globals `gs` with fresh copies `gs_`;
  - `Old.elim` of the body and the postcondition;
  - the goal `All(in ++ out ++ gs, Imp(pre, ...))`;
  - dropping `DeclareProc`/`DeclareVar`.
- `Verify.wp` and `Horn.wp` pass the four exits (normal, break, continue,
  return) separately (→ a record). Horn's `decls`/`clauses` and Verify's
  `gs`/`proc`/`assume`/`commit` are threaded (→ a class per procedure).
- Duplicated helpers:
  - the loop variables `(body.mod ++ attrs.modifies).toList.distinct`
    (`Verify.loop`, `TEQ.modified`);
  - the fresh measures `Expr.vars("m", ...)` (`Verify`, `Horn`);
  - the save and restore of shadowed variables (`TEQ` `Block` and `call`).
- `Monomorph` threads `(state, poly, instances, out)` (→ a class per run). Its
  comment refers to `Sink.known`, which is `Sink.knows`. It replays the whole
  prefix on every flush, which is quadratic for long incremental inputs.
  Keeping the instances across flushes needs a transform with state, which
  `Stage` does not provide.
- `Flat` looks up `datatype(state, ...)` repeatedly with
  `Some(...) = ...: @unchecked`.

### Frontends

- The checks of a procedure are written three times:
  `smtlib.Parser.procedure`, Dafny `MethodDef` and Boogie `ProcDef` (→ one
  helper on `State`). Each checks that it modifies only globals, fixes the
  inputs and the unmodified globals, then calls `progs.check`.
- Dafny and Boogie:
  - Syntax: they share most nodes (literals, `App`, `Inner`, `Ite`,
    quantifiers, `Lam`, `Combinator`, `Sel`, `Constr`, the statements, `Lhs`,
    `Axiom`/`Lemma`, the `Syntax` token object).
  - Resolvers: they repeat the datatype declaration, the update
    `a[i][j] := v` (a verbatim copy), the combinator update with `Eps`
    (written twice in each), the assertion with its remaining type parameters,
    `formula`/`measure`, the statements from `Skip` to `While`, and `Ex`/`All`/`Lam`.
  - Grammars: they repeat `translate`/`avoid`/`Sym`, `nil`/`none`/`true_`/`skip`,
    `some`/`list`/`angle`, and the combinator grammar.
  - (→ a shared syntax, or at least shared resolution and grammar traits.)
- Dafny contracts are separate fields (`mod`, `req`, `ens`, `assumes`,
  `commits`, `dec`) in `FunDef`, `MethodDef` (12 fields) and `While`.
  Boogie's are a list of `Spec` clauses, which Dafny could use too. Dafny
  attributes are names only, Boogie's have arguments.
- Dafny `SeqLit`/`SetLit`/`BagLit`/`MapLit` are four folds of "empty, unit,
  join", mirrored by the four recognizers `elems`/`members`/`multiset`/`pairs`
  of the printer (→ one table of collection literals).
- SMT-LIB parser and printer: the polymorphic (`par`) and monomorphic forms
  of `declare-const`, `declare-fun`, `define-fun`, `assert`, `declare-proc`
  and `define-proc` are separate cases with the same body (→ parse and print
  `par` once). `forall` and `exists` are copies.
- `Source.newParser` of Dafny and Boogie are identical up to the package, and
  `c.Source` repeats Boogie's inline. `yml.Source` parses the C prelude twice.
- Subscripts: `boogie.Grammar.index` turns `a₃` into the string `a$3`, which
  the conversion to `Name` parses again. Dafny relies on that conversion
  alone.
- `c.Parser`:
  - `typ` and `zero` repeat the errors for `void` and `float`;
  - the comment on global variables without initializer sits above `array`
    instead of `zero`;
  - at 889 lines, it mixes the resolution of expressions and statements, the
    inference of modifies (`assigned`, `effects`, `calls`, `writes`) and the
    translation unit, which could be split.
- The flex scanners throw `RuntimeException` on unexpected characters
  instead of `Error`.

### Printers and pipeline

- The mixfix printers of Dafny, Boogie and C share many methods
  (→ a base trait with the operator tables and the terminator as parameters):
  - `name`, `commas`, `call`, `str`, `any`, the five `lines`;
  - `doc(Result)`, the control commands, `format`;
  - `params`, `attribute(s)`, `isClause`, `clauses`, `header`;
  - `braces`, `statements`, `block`, `level`, `doc(expr, context)`;
  - `dependencies`, `combinator`.
- Differences between them:
  - Boogie's error strings replace quotes instead of escaping them;
  - its `isClause` lacks `assumes`/`commits`.
- Recomputed guards: the pattern `case _ if f(expr).isDefined => val Some(...)
  = f(expr): @unchecked` (Dafny `elems`, `members`, `multiset`, `pairs`,
  `prefix`, `comparisons`, `infix`, and the same in Boogie and C) computes `f`
  twice (→ extractor objects, as for `bitvector`/`conversion`).
- Repeated printer cases in Dafny:
  - the update `base[index := value]` is printed by five identical cases;
  - the read `base[index]` by four, `|x|` by four;
  - the operator tables of `Sets` and `Bags` are the same list.
- `smtlib.Printer.attr` and the `any` of the mixfix printers both print
  resolved attribute values.
- `pipe.Printer` has four `lines` overloads for lists.
- `Solver.Sink`:
  - `attrs.retain("named", "pattern")` occurs three times;
  - every case returns `(x, Nil, this)`.
- `util.Tool.pipe` returns `(in, out, ...)` from the process's view, which
  `Solver` binds as `(out, in, ...)`. `Tool.run` and `util.Run` are unused.
- `Pipe.run`:
  - it handles `Error` and `NonFatal` twice, inside the loop and around it;
  - a `StackOverflowError` is not `NonFatal` and escapes as a crash (see
    Bugs);
  - `if (!incremental)` is parenthesized.
- `Config`: every transform flag repeats `config.using(X)`. `flags` is an
  unordered map, so `-help` lists the options in arbitrary order. `suffix`
  returns `null`.
- Global mutable state: the fresh-name counters of `Var` and `Param` (reset
  in `Cuvee.pipe` and `test.Expected`), the printer widths set by
  `-linewidth`, including `sexpr.Printer.width` (hence `-linewidth 80` in
  `Expected`), and `Debug.modules` (→ one context per run).
- `object Debug` (debug output) and `trait Debug` (raising errors, implemented
  by `Error` only) share a name. `raise[A]` has an unused type parameter.
- `easyparse/Sugar.scala` has commented-out extensions; `Mixfix` writes
  `if (...)`.
- Remove `src/cuvee/boogie/Scanner.java~`, an editor backup tracked by git,
  and add `*~` to `.gitignore`.

### Tests

- `rw`, `app` and `R` are defined in `simplify/Rewrite`,
  `simplify/RewriteTraces` and `dafny/TEQ`. `Contexts` defines `simplify`
  three times and shorthands such as `v`, `c`, `P`, `lit`.
- `test.Examples` (`output`, `errors`, `stream`) and `cuvee.test.Expected.run`
  are two harnesses that run a command line in memory.
- No direct tests of easyparse (`Mixfix` precedences and associativity,
  `Repeat`, `Intersperse`) and of `simplify/Arith`.
- Warnings of `mill -i compile`:
  - 444 feature warnings (the implicit conversion `String => Name` without
    `-language:implicitConversions`);
  - 2 deprecations;
  - a possibly non-exhaustive match on `Bind` in `Simplify.scala:129`.

## Solvers

- The stderr of a solver is never read, which can block it.
- Axiomatization of data types: sequences are left to the solvers' theory,
  where quantified specifications often end in `unknown` (e.g. `positive` in
  [examples/dafny/hybrid/par.dfy](examples/dafny/hybrid/par.dfy)), whereas inductive
  axioms, as for datatypes, work better; sequences could be axiomatized
  inductively instead.

## Simplifier and rewriting

- Statements are simplified without context (assignments invalidate facts);
  tests of branches could be used up to the first assignment to their
  variables. No rules for sequences or bitvectors.
- Rewriting matches modulo A/C of `+` and `-` only (not `*`); all but the last
  variable of a sum take one summand or none, a negated last variable takes
  negative summands only; bound variables of combinators are not instantiated
  by conditional expressions; equations of the context are followed only for
  variables inside of the expression (`Chains.chain`, rule `Subst` of the paper),
  not for terms such as `history.events == []`; innermost first, which may
  rewrite subterms before a rule for the whole term applies.
- The goal of [clock.dfy](examples/dafny/hybrid/clock.dfy) remains after
  `-simplify`: the rules of `delay` would need the fact `history.events == []`,
  and `exists s` would need to be instantiated by the time. Plan: replace
  quantified variables of record types, whose selectors occur in the body, by
  their constructor applied to fresh variables (as `Flat` does), with the
  reduction of selectors on constructors.
- Guards below combinators are matched syntactically first, so a bound
  variable that occurs only in guards may match any formula, e.g. `b` matches
  `!b`; lemmas whose guards are more specific must come first (as for
  `counts` in [teq.dfy](resources/cuvee/teq.dfy)).
- Variables that occur only in side conditions of rules or in guards of
  patterns are instantiated by matching the conjuncts against the facts of the
  context (`Context.known`, assumptions and negated conclusions as given, not
  chains or differences) or the conjuncts of the guard of the expression
  (`Rewrite.conditions`), in the order of the conjuncts; open comparisons and
  equations of side conditions are not searched, and the first match is taken
  among several.
- Fourier-Motzkin ([simplify/FourierMotzkin.scala](src/cuvee/simplify/FourierMotzkin.scala))
  is not used yet. Proposal, in this order:
  1. decide `0 <= p`/`0 < p` against the linear facts of the context (the
     comparisons among the assumptions, negated ones among the conclusions)
     in `Simplify.implied`/`denied`, sound on `Int` too, with tightening
     (`0 < p` is `1 <= p`, rounding by the gcd of the coefficients);
  2. mark contexts with unsatisfiable linear assumptions inconsistent;
  3. then redundant bounds vanish by `nary`, e.g. `x <= 3 && x <= 5`;
  4. eliminate `exists x` over linear constraints where the number of
     constraints does not grow (`l <= 1` or `u <= 1` bounds), exact on `Real`,
     on `Int` for coefficients ±1;
  5. limit the number of constraints (e.g. 20).
- A lemma that is an equation of integers, e.g. `2 * s == n + n * n`, is a
  rule on its left-hand side as a term, not on the atom; equivalences of atoms
  work (see [gauss_sum.dfy](examples/sv-comp/loop-new/gauss_sum.dfy)). A
  monomial such as `2 * s` inside a polynomial is not matched against the
  definition `s == e` of the context.
- A comparison pattern `b < x` with `b` open does not match `k < x + n`,
  where `b` would be the difference `k - n`, while `0 < x + c` matches with
  `c := n - k` (see
  [benchmark04_conjunctive.dfy](examples/sv-comp/loop-zilu/benchmark04_conjunctive.dfy)).
- A higher-order pattern as a summand, e.g. `G(k)` in `G(k) + b[k]`, matches
  a single summand of the expression, not several, e.g. not `2 * k + 3` in
  `b[k] + 2 * k + 3`, and a variable as the coefficient of a monomial does not
  match a literal coefficient, such that affine updates are not matched
  generically (see [sqm.dfy](examples/sv-comp/array-fpi/sqm.dfy)).
- Rules on a comparison do not match its negation, e.g. a rule for
  `0 <= e` does not apply to `e < 0` (on `Int`, `e + 1 <= 0`), such that
  lemmas are stated in both forms.
- Hypotheses are not split into cases: `X == (if c then A else B)` and
  disjunctions among the hypotheses remain, `-split` followed by another
  `-simplify` splits them (see
  [diamond_1-1.dfy](examples/sv-comp/loop-acceleration/diamond_1-1.dfy),
  [half.dfy](examples/sv-comp/loop-new/half.dfy)).
- Linear facts over more than two variables are not combined: the context
  `n0 <= 0`, `n1 <= 0`, `0 < n0 + n1` is not found inconsistent, since
  `n0 + n1` is no difference constraint (`Diffs`), while `FourierMotzkin`
  would decide it (see [seq-3.dfy](examples/sv-comp/loop-invgen/seq-3.dfy)).
- Expressions with binders are compared literally, not modulo the names of
  their bound variables: `count(0, maps(for ⌊K⌋, ⌊L⌋ yield k₁₀, l₈ :: k₁₀ % 2))`
  and the same with `k, h`, which the right-hand side of a rule introduces,
  are not found equal (see [sumt2.dfy](examples/sv-comp/loops-crafted-1/sumt2.dfy)).
- Expressions are compared literally, also modulo the definitions of the
  context: `sum(selects(x, ⌊K⌋))` and `sum(selects(x, ⌊counter(0, 1, 100)⌋))`
  with `K == counter(0, 1, 100)` are not found equal, since definitions are
  followed in matching only (`Context.↑`), and a side condition
  `ks == ⌊counter(0, 1, m + 1)⌋` with `ks := ⌊K⌋` is not decided (see
  [mapsum1.dfy](examples/sv-comp/array-crafted/mapsum1.dfy)).
- The branches of a conditional formula are not simplified under the facts
  of the context: `r != 0 ==> if a then 1 == r else 0 == r` stays, while
  `r != 0 && 0 == r ==> p` is closed; nor is a disjunction among the
  hypotheses, `(a && 1 == r || !a && 0 == r) && r != 0` (see
  [standard_password_ground.dfy](examples/sv-comp/array-examples/standard_password_ground.dfy)).
- `-split` also splits lemmas marked `{:rw}`, e.g. an equivalence with a
  conditional on its right-hand side, into parts that are no valid rules, on
  which a following `-simplify` fails with "variables of right hand side do
  not occur in left hand side or condition".
- Reads over writes at a different position are decided in the neutral
  context (`Simplify.select` with `ctx.neutral`), without the facts: `j != 3`
  among the hypotheses does not reduce `a[3 := w][j]` to `a[j]`; a lemma
  `if j != i then a[i := v][j] == a[j]`, whose side condition is decided
  against the facts, does (see
  [single_elem_safe.dfy](examples/sv-comp/array-lopstr16/single_elem_safe.dfy)).
- Conditionals inside equations and products are not lifted, e.g.
  `(if c then x else n) == (if c then x * x else n)`; a lemma for equations of
  conditionals with the same test applies, but one for the product
  `(if c then x else y) * (if c then x else y)` does not match, presumably
  since products of conditionals are monomials of the polynomial (see
  [motivex.dfy](examples/sv-comp/array-lopstr16/motivex.dfy)).
- Facts with coefficients are not combined: `n₁₄ <= 200000` and
  `100000 < n₆` do not give `n₁₄ < 2 * n₆`, since difference constraints
  have unit coefficients; nor is an interval `100000 < n₆ < 100002` on Int
  narrowed to `n₆ == 100001` (see
  [array_doub_access_init_const.dfy](examples/sv-comp/array-cav19/array_doub_access_init_const.dfy)).
- A pattern sum of a rule variable and a bound variable, e.g. the position
  `c - k` of a store in an update, matches only if the variable takes a single
  summand: `S + -k` matches, `2 * S + -k + -1` and `S + -k + -1` do not, nor
  does the pattern `c - 1 - k` (see
  [array_tiling_tcpy.dfy](examples/sv-comp/array-cav19/array_tiling_tcpy.dfy)).
- A lemma for a monomial with a coefficient, e.g.
  `2 * ((-x + x * x) / 2) == -x + x * x`, does not match that monomial inside
  an equation, `n * n == 2 * ((-n + n * n) / 2) + n`, presumably since
  equations are normalized as differences of polynomials (see
  [ps2-ll.dfy](examples/sv-comp/nla-digbench/ps2-ll.dfy)).
- Conjunctions are matched in order, not modulo commutativity: a pattern `R && A && B ==> C`, with a variable `R`
  for the other premises, matches `u < 3 && A && B ==> C`, but neither `A && u < 3 && B ==> C`, nor
  `A && B && u < 3 ==> C`, nor `u < 3 && B && A ==> C`; further variables between them, `R1 && A && R2 && B && R3`,
  do not help. Lemmas that need two premises of a goal therefore depend on the order in which the simplifier
  emits them (see [seq-3.dfy](examples/sv-comp/loop-invgen/seq-3.dfy), where the order fits). Chains of comparisons are
  conjunctions already (the parser resolves them), only printed as chains. Premises are looked up at any position
  as side conditions instead (`Rewrite.conditions`), also comparisons, e.g. `requires 2 * a + p <= b + 2 * c &&
  c < a` with `ensures (p + 1 < b) <==> true`, as in MADWiFi-encode_ie_ok; this form does not work for seq-3,
  whose rule `0 < a + b` also matches a single summand and decides its side condition by itself.
- No integer rounding: `2 * n <= 2 * k + 1` does not give `n <= k`; no
  cancellation of a factor, e.g. `k * j < 1000000 * k`, and a lemma
  `if 0 <= k then (k * a < k * b) <==> (0 < k && a < b)` does not match it,
  since a variable of a pattern does not match the coefficient 1000000 of the
  monomial `1000000 * k` (see [count_by_k.dfy](examples/sv-comp/loop-new/count_by_k.dfy)).

## Performance

Measured on binary search with forward rules (branch `forward`) and on the
SV-COMP examples (`examples/sv-comp`):

- The rewrite steps per command are limited to 1000 (`Context.withRules`),
  and an exhausted budget is reported as "rewriting does not terminate",
  like a stack overflow, although rewriting may terminate.
- The negation of an equation on Int asks the context for both bounds (`Simplify.not`), which made 14 SV-COMP tasks
  time out, one of them closed before (`string-1`); a cheaper check would only look at the bounds that the
  difference constraints already have.
- Guards of updates are decided by the simplifier with all rules
  (`Rewrite.guard`, `Rewrite.holds`), about 20 ms each. Failing decisions
  are the expensive ones, and identical decisions are repeated without a
  cache: 864 decisions, 15 of them distinct, in one run of binary search.
- `Rewrite.conditions` simplifies each conjunct of a side condition, also
  one in which no variable is instantiated yet. Then it rewrites the open
  pattern with all rules, e.g. `X == trace(...)` as the premise of a forward
  rule. This is fixed on `forward` only.
- Matching an equation tries both orders. With the definition of a variable
  (`Context.↑`), `X == trace(...)` matches `Lo == trace(...)` twice, the
  second time with `X` bound to the trace. This is fixed on `forward` only.
- `Simplify.nary` simplifies each conjunct under all others. With forward
  rules in `Context.assume`, every sibling context derives the same
  conclusions again, which took binary search beyond 10 minutes; on
  `forward`, siblings are recorded without forward rules.
- Each round of the fixpoint of `Simplify.apply` simplifies the whole
  formula again. Programs with many loops grow accordingly, e.g.
  [standard_copy9_ground-2.dfy](examples/sv-comp/array-examples/standard_copy9_ground-2.dfy)
  takes about 20 s for a chain of nine copies, against about 2 s for one copy.
- Non-termination is detected by a stack overflow only, after 8 to 13 s,
  e.g. on counts over prefixes (see Bugs). The symbolic execution of `-teq`
  is exponential in sequences of conditionals and overflows at ten (see Bugs).

## Trace equation systems (`-teq`)

- The functions on traces are declared only by the lemma database
  ([teq.dfy](resources/cuvee/teq.dfy)), whose names may clash with the input,
  and which only Dafny inputs can use (`Config.features`).
- The guards of the updates of traces are the branch conditions of the body
  only; the loop test and assumptions in the body are recorded in `invs`
  (`TEQ.loop`), which the simplifier and the matching assume in the update of
  `X == trace(...)` (`Simplify.invariants` with `self`), but not for traces
  that are not the right-hand side of such an equation.
- The guarded cases of an expression are matched in their order, each against
  some case of the pattern, such that a higher-order guard bound by a later
  case of the pattern is still open when an earlier case of the expression
  needs it.
- Facts about terms are not derived (see [doc/simplifier.md](doc/simplifier.md#forward-reasoning));
  bsearch.dfy needs a cut, `assert φ; assume φ;`, and `-teq`
  does not assume assertions.
- The simplifier evaluates integer division on literals and divides by
  literals on Real, but knows no bounds of division, e.g. `l <= (h + l) / 2`
  for `l <= h` is a lemma in bsearch.dfy, nor cancels factors,
  e.g. `2 * n / 2` (see
  [mlceu2.dfy](examples/sv-comp/array-tiling/mlceu2.dfy),
  [array_of_struct_ptr_monotonic.dfy](examples/sv-comp/array-industry-pattern/array_of_struct_ptr_monotonic.dfy)).
- Solutions of arithmetic equations are inlined into polynomials only
  (`Chains.solved`), not substituted elsewhere, e.g. `forall x. x == y + 1
  ==> p(x)` stays; a solution that depends on its variable through the
  equations of the context is not inlined (`Chains.acyclic`).
- Higher-order patterns (`Rewrite`) take distinct bound variables or terms
  instantiated already as arguments; other arguments match only if an
  earlier occurrence instantiated the variable, and a single bound variable
  of the pattern cannot abstract several of the expression (no tuples).
  Terms are abstracted at all of their occurrences.
- No instantiation of the iteration constraint at a witness, e.g. a search
  whose constraint states that `P` holds before the exit `n`, and `!P(j)`,
  which gives `n <= j`; the examples abstract the constraint by an atom first,
  e.g. `!occurs(e, selects(a, ⌊counter(0, 1, n)⌋))` by `not_occurs_selects_def` of teq.dfy, which a second lemma
  takes as its side condition (see
  [standard_sentinel-2.dfy](examples/sv-comp/array-examples/standard_sentinel-2.dfy)),
  since a side condition that is an iteration constraint does not terminate;
  a forward rule on branch `forward` would instantiate it directly.
- Nested loops: the outer trace takes the values of summarized inner traces,
  whose composition, e.g. `k == n * m`, is not accelerated (see
  [nested-1.dfy](examples/sv-comp/loop-new/nested-1.dfy)).

## Dafny frontend

- Containers: missing comprehensions, `multiset(s)`, the multiset update
  `m[x := n]`, `>=` and `>`, disjointness `!!`, `seq(n, f)`, and
  multi-dimensional updates.
- `x.f` and `x.C?` on variables only; members inside `type`/`datatype` bodies
  need `this.` ([examples/datastructures/stack.dfy](examples/datastructures/stack.dfy)). The
  qualified name `T_f` comes from the declared sort of the variable, before
  type checking. Plan:
  1. testers `e.C?` on terms: the constructor determines the datatype
     (`state.exprs.is`), drop the restriction to variables;
  2. unqualified members in type bodies: with `this: T` in scope, `f(args)` is
     `T_f(this, args)` and `y := m(args)` calls `T_m(this, args)`, with
     Dafny's precedence: locals, members of `T`, top-level functions;
  3. functions and selectors on terms: the parser emits a generic
     application `.f` with fresh types and the receiver first, `Type.check`
     records it as pending, and `Overload.resolve` looks up `T_f` in
     `state.funs` by the sort of the receiver, extending `impl` by a lookup
     in the state; a receiver whose type is still a parameter is an error;
  4. method calls on terms (`y := f(x).m()`) need the receiver's sort when
     the statement is built: type check the receiver on its own, otherwise
     keep the restriction; last;
  5. tests: [stack.dfy](examples/datastructures/stack.dfy) without `this.`, nested
     accesses `f(x).g()`, errors for unknown receivers.
- `var` declarations before statements; contract clauses in the fixed order
  `modifies`, `requires`, `ensures`, `assumes`, `commits`, `decreases`, for
  loops `modifies`, `invariant`, `decreases`.
- `t.0.1` is scanned as `t` `.` `0.1`.
- The printer's `any` raises `MatchError` on plain strings and numbers.
- Names that are neither identifiers nor operators, e.g. the instances
  `f<Int>` of `-monomorph`, are escaped by backticks, which the scanner reads
  back but Dafny does not have; names containing backticks are not handled.
- Dafny printed from C input (`-print dfy`) is not parsed back: the prelude
  declares a function named `const` with type parameters,
  `function {:c} {:smt2} const<a₀, a₁>(x₀: a₁): array<a₀, a₁>`.
- Parse errors of `fuse` show the term in the internal syntax of the parser
  (`Inner(App(...))`).

## Boogie frontend

- Procedures must be declared before calls (no mutual recursion); no
  `forall<a>`, sequences, or parallel composition.
- Datatypes (`data`, not Boogie) have no testers and no `match`; `data`,
  `and`, and `|` are keywords.
- z3 answers `unknown` for Horn clauses over recursive datatypes
  ([examples/boogie/vcgen/data.bpl](examples/boogie/vcgen/data.bpl)).
- The printer rejects loop attributes other than `invariant`,
  `modifies`, `decreases`, other binders, derivatives, ODEs, and `par`;
  `goal`, `lemma`, `decreases`, `continue` are printed although not Boogie.

## C frontend

Subset of C without memory ([c/](src/cuvee/c), [examples/c](examples/c)).

- Unbounded integers, no overflow; arrays are values, sizes are ignored.
- `goto` only to a label whose statement does not fall through (e.g.
  `END: return 0;`, `ERROR: { reach_error(); abort(); }`), which is copied in
  its place, or to itself (a loop without exit); other gotos, e.g. those of
  state machines, are not supported (`c.Parser.goto`).
- `sizeof` of an expression by the declared integer type and array sizes of
  its variable (`c.Parser.bytes`), otherwise by its type.
- No structs, floating point, bitwise operators, preprocessor; pointers
  only as arrays allocated by `malloc`, `alloca`, `calloc` (see [SV-COMP.md](SV-COMP.md)), and otherwise as values of `Ptr`
  in the prelude of C ([prelude.bpl](resources/cuvee/c/prelude.bpl)), which
  are compared but not dereferenced; no `&`, `*p`, or pointer arithmetic.
- The modifies clause of a loop is inferred from the core program, where a
  local variable that shadows a global one of the same type counts as global.
- z3 answers `unknown` for Horn clauses with division by variables
  ([examples/c/vcgen/div.c](examples/c/vcgen/div.c)), and for calls in loops whose
  callee has no goals, since its precondition is inferred from the calls
  (only uncalled procedures are entry points).
- Errors of the C frontend on SV-COMP (Arrays and Loops, 0.34.22, 101 tasks;
  with 0.35.2, 3 parse: `loops/compact`, `heavy-1`, `heavy-2` by `sizeof` of
  expressions), besides `goto` to labels that fall through (26, see New;
  most are gotos back in the outputs of the reducers, which could be loops
  `L: while (true) { ...; break; }` whose gotos continue them, without
  copies), and floating point (29, also float literals now report "not
  supported"):
  - Structs and unions end in a generic parse error, not in "not supported"
    (37 tasks: definitions and forward declarations `struct S;` at the top
    level, `typedef struct {...} *T`, an anonymous `struct { int n; } a[]`
    as parameter, e.g. `array-lopstr16`,
    `array-industry-pattern/array_of_struct_*`, `loop-industry-pattern/aiob_*`,
    `ofuf_*`, also `union wait` of the headers in `array-examples/relax-2-2`).
  - Deeply nested `if`/`else` (about 240 levels in the outputs of the
    reducers) overflowed the stack; `Cuvee.main` now runs on a thread with a
    stack of 1 GB, and `c.Parser.effects` iterates over the statements of a
    block; these tasks now end at gotos. Tests call `Cuvee.pipe` directly,
    on the default stack.
  - `*p` in `p <= tmp` with pointers is "not an integer"
    (`loops/verisec_NetBSD-libc_loop`, `veris.c_NetBSD-libc_loop`); `&x` and
    `*p` otherwise report "not supported".
  - Arrays of pointers are not supported (`array-industry-pattern/array_ptr_partial_init`,
    `array-lopstr16/partial_lesser_bound`).
  - A pointer that is assigned a local array, `char in[11]; char *s; s = in;`,
    is a type mismatch of `PointerType` and `ArrayType`
    (`loops/veris.c_sendmail_tTflag_arr_one_loop`).
  - GCC builtins are unknown functions, e.g. `__builtin_bswap32`
    (`array-examples/relax-2-2`).

## SV-COMP task definitions

- The properties and expected verdicts of a task (`Task.properties`) are read
  but not used; only a single input file in C is supported.

## Bitvectors

`BitVec(n)` with the SMT-LIB literals and functions (`BitVecs`). Open: no
simplifier rules; widths cannot be parameters.

- Return to the bitvectors of Dafny: the test suites over
  `examples/dafny/vcgen` (`SimplifyPrograms`, `Verify`, `Split`) reported
  "goal does not hold" for [bitvectors.dfy](examples/dafny/language/bitvectors.dfy)
  sometimes in the full test run, depending on the tests run before it in the
  same JVM; alone, and with `java -jar cuvee.jar -simplify -verify -z3`, it
  passes. The fresh-name counters are reset per run (`Cuvee.pipe`), so some
  other state persists across runs. The example is moved out of `vcgen`,
  hence no suite runs it.

- Dafny: no `<<`, `>>` (as a token, `>>` would close nested type arguments
  `seq<seq<int>>`), no infix `|` (which clashes with `|s|`), no
  `RotateLeft/Right`, no `bv0`; `x as int < n` parses `int<` as type
  arguments, it needs parentheses.
- Boogie proposal: types `bv8`, literals `5bv8`, `x ++ y`, `x[8:0]` (exclusive
  upper bound), and functions declared with `{:bvbuiltin "bvadd"}` resolved to
  the instance of `BitVecs.fun`.

## Parallel composition

- `Horn` rejects `parallel` and ignores assumptions and commitments.
- Sequential calls neither establish the callee's assumption nor guarantee
  its commitment (unsound); commitments are checked only at `send`/`receive`/`tick`
  directly in the body.
- The results of `send`, `receive`, and `tick` must be assigned to the global
  `history`, which is not checked.
- Only calls can be composed.
- Neither `tick` nor `delay` has a test.
