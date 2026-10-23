# TODO

Open problems, limitations, and planned work, grouped by area; bugs (wrong results, errors, crashes,
non-termination) are in [bugs.md](bugs.md), the architecture in [doc/architecture.md](doc/architecture.md).

## New

- The algorithms of examples/dafny/algorithms under `-teq -prove` (Oct 16, 2026): 27 of 30 are verified; open are
  max_element (an existential postcondition, no witness), cocktail_sort and counting_sort ("rewriting does not
  terminate"); their lemmas were written for one trace per variable (verified with `-teq -simplify` on Oct 11) and do not
  match since `-teq` closes nested loops (one trace per component, Oct 13).
- `-prove`: with `natural_positive` (teq.dfy), the rounds of simplification of array-crafted bAnd*, bor*, xor* (15
  tasks, unknown before) do not settle and use up the 1000 steps ("rewriting does not terminate"): the same reads
  `x[0]`, `x[1]` are rewritten in every round, `integer(n)` to `i` by integer_natural modulo the class of `n`; a rule
  `natural(x) == zero <==> x <= 0` instead does the same
- `-prove` does not refute a goal by substituting a variable that a premise equates with a constructor, e.g.
  `not (n == zero && 0 <= integer(n))` of while_infinite_loop_4 (expected false)
- sum_by_3 and sum_by_3_abstracted stay open under the case splits of `-prove` (0.46.12, which closed in-de20 by
  splitting `n == zero || integer(n) < 1`)

- support verifying trace lemmas in Dafny
- identify performance improvements, notably in the simplifier
- thread config through more code, so that it is usually available
- error messages should use a nice printer
- witness output: SV-COMP scores verdicts without a validated witness with 0
  (doc/paper/README.md); correctness witnesses need loop invariants (from
  the models of Z3 for `-chc`, or derived from the trace equation systems),
  violation witnesses a path (from the counterexamples of `-chc`); the
  analysis and plan in [ideas/witnesses.md](ideas/witnesses.md); see
  "Portfolio of TEQ and CHC" below
- SV-LIB, whose program syntax the SMT-LIB frontend shares (see doc/architecture.md), lacks
  unstructured control flow (labels and gotos, e.g. by a loop over a program
  counter, with the invariants of labels as `pc = k ⇒ φ`), `define-procs-rec`,
  tags on statements other than loops, procedure bodies and sequences (0.39.0:
  `(! (sequence ...) :tag t)` is a `core.Block` with attributes, whose
  `check-true` annotations `State.annotated` asserts at its beginning, as the
  translated C tasks of SV-COMP use for their assertions; the printers of C,
  Boogie and Dafny drop the attributes of blocks), the liveness
  properties `:recurring` and `:not-recurring`, which 6 of the 7 core
  verification tasks use, and `:decreases-lex`, `get-witness` (the query
  `GetWitness`, answered `unsupported`; see witness output) and
  `select-trace`, the answers `correct`/`incorrect` to
  `verify-call` for interactive use (the verdict is decided by cuvee.py),
  constants in the bodies of procedures with `-chc` (Horn solvers reject free
  constants, the entry clause quantifies only those of the arguments and
  axioms); a dangling tag is an error, the report says to ignore it
- The modified global variables of procedures and loops are inferred by the
  parser (`smtlib.Parser.modifies`), and a body may list them as
  `:modifies`; the inference belongs into the verification (`VCGen`,
  `TEQ`, `Horn`), such that the parser keeps what is written. Procedures
  without body (`declare-proc`) list them, there is nothing to infer from.
- SV-COMP tool entry and zenodo archive: the archive of 0.41.4 is published
  (10.5281/zenodo.23317707, in fm-tools `data/cuvee.yml`, merge request !1176,
  and in doc/paper); it predates the entry points (25c90e96), without which
  `-teq` checks functions out of the context of their calls
  (`sanfoundry_24-1`, `verifythis/lcp` answered `incorrect`): package and
  upload a new version (`scripts/zenodo.py package`, `upload`, published by
  hand) and enter its DOI in fm-tools and doc/paper. The experiments of the
  paper loaded all modules of the database (`-include teq:nested`, `sorting`, since
  renamed `sorted`, `strides`), the options in fm-tools do not: align them. The tool-info module
  `cuvee.py` is the pull request sosy-lab/benchexec#1327 (branch `add-cuvee`
  of github.com/gernst/benchexec), to be kept in sync with this repository

## General

- Function types (`arrow₁`, ...) and their applications (`apply₁`, ...)
  are printed and parsed in SMT-LIB as those of SMT-LIB 2.7, `(-> A B C)`
  and `(@ f a b)`; they are marked `{:ho}` and their declarations are not
  passed to solvers, which hardly support them.
  Lambdas of SMT-LIB are arrays of a single variable, since solvers support
  only those, hence lambdas of function type printed in SMT-LIB are not read
  back.
- `-monomorph` keeps polymorphic assertions uninstantiated (`Monomorph`), which
  the solvers reject; hence no z3 on polymorphic input (CLAUDE.md).
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
- `Match`: parsed only in Dafny (expressions, without case conditions, not
  statements), printed in Dafny and SMT-LIB without case conditions; the
  simplifier does not reduce it on constructors (only `Fuse` selects cases),
  no rewriting modulo matches.

## Proofs of teq.dfy in Lean

- The proofs are in [lean/](lean) (doc/teq.md): the statements of the lemmas of the stable modules (teq.dfy,
  aggregation, arithmetic, search, sorted, arrays, counters, strides, unsigned) are generated from them
  (`scripts/lean/generate.py`), the proofs are by hand, and `scripts/lean/check.sh` checks that each lemma is proved
  as printed. All are proved ([lean/open.txt](lean/open.txt) is empty), no `sorry` remains; the
  counterexamples show the premises that are needed: dependencies of equal length, indices within the lists, and
  complete guards. `cut` and the predicates of sorted.dfy have definitions in the modules (no rules), which the proofs
  use.
- The premises that the engine does not check (lean/premises.txt), the disjointness of guards, and the lemmas without
  a proof are in bugs.md (Soundness, Trusted without a check).
- The bisection of search.dfy is a total definition with `{:fold}` since Oct 14, 2026, whose bounds are proved
  (bugs.md, Fixed); `-print lean` prints its trace of two accumulators as a trace of a product.
- The check from scratch takes about 20 s, mostly `simp` and typeclass inference for the decidability of `if` on generic
  types under `open Classical`; `simp only` instead of `simp` would speed it up.
- Open (formerly ideas/teq-lean.md):
  - The nine index premises of `lean/premises.txt` (reads and prefixes within the loop) as `requires` of the
    lemmas, if `-prove` decides `integer(k) < integer(n)` in the contexts of the goals; measure each on `mill -i
    test` and the SV-COMP rows that use it. The length premise of `earlier_not_occurs_prefix` stays (the engine knows no
    lengths). For now only documented (decision of the user, Oct 13, 2026).
  - A test in `mill -i test` that generates `Database.lean` in memory and compares it with the committed one, so that
    a change of a stable module fails the Scala tests without Lean (`generate.py --check` does it on request).
  - The legacy theorems of `Proofs.lean` (lemmas of `legacy/teq.dfy` no longer in the stable modules): a frozen
    `Legacy.lean`, or dropped with the legacy database.
  - The definitions of `cut` and of the predicates of sorted.dfy fix one meaning of functions that the engines use
    through their lemmas only (`cut` on an empty interval, `lower` as the cut of `ar[j] < y`).
  - A Lean mode of the printer (`Stmt` definitions and the preamble) instead of the text manipulation of
    `generate.py`; the comments of `lean.Printer` still refer to the former `resources/cuvee/teq.lean`.
  - Guards are printed as `if g₁ then e₁ else if g₂ then e₂ else unspecified` (0.46.11); overlapping guards take
    the first case.

## Printers

- The Lean printer (`-print lean`) prints no preamble: the output needs
  `open Classical` and Mathlib (`ℝ`, `Set`), and names of the input that
  Lean declares already clash, e.g. a datatype `List` or a function `max`,
  which a namespace around the output would avoid. Only the modules of the
  database are checked with Lean, through scripts/lean/generate.py, which adds
  the preamble.
- The C printer of the Dafny translations of SV-COMP
  (`benchmarks/sv-comp/dafny`, `-print c -known dfy,teq,rw`): all 651 print as
  C that parses again (`benchmarks/sv-comp/c`), whose programs, printed back as
  Dafny, are those of their sources. The translations use `quot` and `rem` of
  the prelude of Dafny for the division and remainder of C, have no global
  variables where C would initialize them to zero (`loops/eureka_05`,
  `n.c40`, `nec40`), and fill the constant arrays of C by loops with arbitrary
  values (`loops/vogal-1`, `vogal-2`, `eureka_01-2`).

## Code structure

Opportunities for cleaning up, making the code uniform, and merging common
concepts, found by reading the whole code base; none is a bug. The simplifier is
the traversal of `-prove` (package `prove`); the former package `simplify` was
removed on Oct 23, 2026.

### Core

- `Prog.subprogs` is a second traversal of programs next to `Prog.map`,
  for three recursive queries that each special-case a statement or two
  and recurse through it otherwise: `Prog.modifies` (which matches `Block`
  as well), `VCGen.abstracts`, and `calls` inside `c.Parser.while_`. The
  queries could be members like `mod`, `free` and `funs`, or use one fold
  over the children, together with the generic traversal of expressions
  below.
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
- `Fun` equality includes the names of the formals (the overrides of
  `equals` and `hashCode` are gone), hence the formals of constructors are
  `x₀`, `x₁`, ... in all frontends, as in `Fun`, and so are those of the
  functions of `teq.dfy`. Open:
  `Fuse.fuse` gives its `Rec` the variables of the request as formals, while
  the cases call `hf` with formals `ff.formals ++ ys`, so `Rec.funs`
  (`- fun`) keeps the recursive calls, `Rec.retype` (`fun_ == fun`) sees a
  change, and the patterns of `Type.check(Rec)` do not apply `fun`; `Fuse`
  should keep `hf` and rename its cases instead. `legacy/teq.dfy` and
  `legacy/core.dfy` still use other names.
- `Subst.apply(attrs)` maps expressions only, so `modifies` lists are neither
  renamed nor retyped, while `Type.expand(attrs)` handles them
  (→ `Attrs.map` with a function for variables).
- `State` keeps a declaration, attribute and definition map per kind (sorts,
  functions, variables, procedures). Each repeats the checks "already
  declared" and "not declared" (→ one generic table). `exprs.trace`, `map`
  and `all` repeat the creation of the bound variables.
- `history`: `State.history` exists, but `Prog.Par`, `Type.check(Ode)` and
  `VCGen.tick` look up `state.vars.get("history")`.
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

- Abstractness for the answers comes from two sources. A goal is
  `:abstract` when `VCGen.abstracts` finds a loop without invariant, or when
  `Fallback` lowered it. A function is abstract when declared `:abstract`
  (the C bit operations) or defined in terms of one; the solver sink collects
  those in `abstracts` while the stream passes, from `Cmd.funs`. That
  closure follows the order of the stream, so a definition never sees an
  abstract function that comes after it, e.g. in mutual recursion. It is
  also the only reason for `Expr.funs` and `Cmd.funs`, whose other cases
  (`FuseFuns`, patterns, `Rec`) nobody reads. The functions could be marked
  once in the `State` when they are defined, and the frontends or `VCGen`
  could mark the goals that apply them. `Verify` would then test the goal's
  attribute only, and the two names `abstracts` (programs in `VCGen`,
  functions in `Verify`) would go.
- `VCGen`, `TEQ` and `Horn` repeat the setup of a procedure (→ one helper):
  - the contract and the globals `gs` with fresh copies `gs_`;
  - `Old.elim` of the body and the postcondition;
  - the goal `All(in ++ out ++ gs, Imp(pre, ...))`;
  - dropping `DeclareProc`/`DeclareVar`.
- `VCGen.wp` and `Horn.wp` pass the four exits (normal, break, continue,
  return) separately (→ a record). Horn's `decls`/`clauses` and VCGen's
  `gs`/`proc`/`assume`/`commit` are threaded (→ a class per procedure).
- Duplicated helpers:
  - the loop variables `(body.mod ++ attrs.modifies).toList.distinct`
    (`VCGen.loop`, `TEQ.modified`);
  - the fresh measures `Expr.vars("m", ...)` (`VCGen`, `Horn`);
  - the save and restore of shadowed variables (`TEQ` `Block` and `call`).
- `Monomorph` threads `(state, poly, instances, out)` (→ a class per run). It replays the whole
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
  - at 1743 lines, it mixes the resolution of expressions and statements, the
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
  `Solver` binds as `(out, in, ...)`. `Tool.run` is unused.
- `Pipe.run`:
  - it handles `Error` and `NonFatal` twice, inside the loop and around it;
  - a `StackOverflowError` is not `NonFatal` and escapes as a crash (see
    bugs.md);
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

- `rw`, `app` and `R` are defined in `prove/Rewrite`,
  `prove/RewriteTraces` and `dafny/TEQ`. `prove/Simplify` defines `simplify`
  three times and shorthands such as `v`, `c`, `P`, `lit`.
- `test.Examples` (`output`, `errors`, `stream`) and `cuvee.test.Expected.run`
  are two harnesses that run a command line in memory.
- No direct tests of easyparse (`Mixfix` precedences and associativity,
  `Repeat`, `Intersperse`) and of `prove/Arith`.
- Warnings of `mill -i compile`:
  - 444 feature warnings (the implicit conversion `String => Name` without
    `-language:implicitConversions`);
  - 2 deprecations;
  - a possibly non-exhaustive match on `Bind` in `Simplify.scala:129`.

## Solvers

- Axiomatization of data types: sequences are left to the solvers' theory,
  where quantified specifications often end in `unknown` (e.g. `positive` in
  [examples/dafny/hybrid/par.dfy](examples/dafny/hybrid/par.dfy)), whereas inductive
  axioms, as for datatypes, work better; sequences could be axiomatized
  inductively instead.

## Simplifier and rewriting

- A lemma that defines an auxiliary predicate by an iteration constraint with a general body, e.g.
  `invs(... :: x <= b) <==> below_prefix(n, xs, b)`, matches the bound of every loop, `x < N` as `x + 1 <= N`
  (the body generalized to a map), and hides it from the lemmas on traces (`loop-acceleration/diamond_1-1`), hence
  such definitions stay local to the tasks (`loop-invariants/linear-inequality-inv-*`).
- The pattern `a + b * v` of `maps_counter_affine` does not match `N + -k + -1` with `b == -1`, and a map with a
  further dependency that its body does not use matches no lemma on a map of the counter alone, hence the local
  lemmas `occurs_1` and `indexof_1` of `array-cav19/array_init_both_ends_multiple_sum`; general variants of the
  lemma did not help and made `array_init_var_plus_ind2` open.
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
  `-prove`: the rules of `delay` would need the fact `history.events == []`,
  and `exists s` would need to be instantiated by the time. Plan: replace
  quantified variables of record types, whose selectors occur in the body, by
  their constructor applied to fresh variables (as `Flat` does), with the
  reduction of selectors on constructors.
- Guards below combinators are matched syntactically first, so a bound
  variable that occurs only in guards may match any formula, e.g. `b` matches
  `!b`; lemmas whose guards are more specific must come first (as for
  `counts` in [aggregation.dfy](resources/cuvee/teq/aggregation.dfy)).
- Variables that occur only in side conditions of rules or in guards of
  patterns are instantiated by matching the conjuncts against the facts of the
  context (`Context.known`, assumptions and negated conclusions as given, not
  chains or differences) or the conjuncts of the guard of the expression
  (`Rewrite.conditions`), in the order of the conjuncts; open comparisons and
  equations of side conditions are not searched, and the first match is taken
  among several.
- A lemma that is an equation of integers, e.g. `2 * s == n + n * n`, is a
  rule on its left-hand side as a term, not on the atom; equivalences of atoms
  work (see [gauss_sum.dfy](benchmarks/sv-comp/dafny/loop-new/gauss_sum.dfy)). A
  monomial such as `2 * s` inside a polynomial is not matched against the
  definition `s == e` of the context.
- A comparison pattern `b < x` with `b` open does not match `k < x + n`,
  where `b` would be the difference `k - n`, while `0 < x + c` matches with
  `c := n - k` (see
  [benchmark04_conjunctive.dfy](benchmarks/sv-comp/dafny/loop-zilu/benchmark04_conjunctive.dfy)).
- A higher-order pattern as a summand, e.g. `G(k)` in `G(k) + b[k]`, matches
  a single summand of the expression, not several, e.g. not `2 * k + 3` in
  `b[k] + 2 * k + 3`, and a variable as the coefficient of a monomial does not
  match a literal coefficient, such that affine updates are not matched
  generically (see [sqm.dfy](benchmarks/sv-comp/dafny/array-fpi/sqm.dfy)).
- Rules on a comparison do not match its negation, e.g. a rule for
  `0 <= e` does not apply to `e < 0` (on `Int`, `e + 1 <= 0`), such that
  lemmas are stated in both forms.
- Hypotheses are not split into cases: `X == (if c then A else B)` and
  disjunctions among the hypotheses remain (`-prove` splits disjunctions, and the guards of updates since 0.46.16),
  `-split` followed by another `-prove` splits them (see
  [diamond_1-1.dfy](benchmarks/sv-comp/dafny/loop-acceleration/diamond_1-1.dfy),
  [half.dfy](benchmarks/sv-comp/dafny/loop-new/half.dfy)).
- Linear facts over more than two variables are not combined: the context
  `n0 <= 0`, `n1 <= 0`, `0 < n0 + n1` is not found inconsistent, since
  `n0 + n1` is no difference constraint (`Diffs`), while `FourierMotzkin`
  would decide it (see [seq-3.dfy](benchmarks/sv-comp/dafny/loop-invgen/seq-3.dfy)).
- Expressions with binders are compared literally, not modulo the names of
  their bound variables: `count(0, maps(for ⌊K⌋, ⌊L⌋ yield k₁₀, l₈ :: k₁₀ % 2))`
  and the same with `k, h`, which the right-hand side of a rule introduces,
  are not found equal (see [sumt2.dfy](benchmarks/sv-comp/dafny/loops-crafted-1/sumt2.dfy)).
- Expressions are compared literally, also modulo the definitions of the
  context: `sum(selects(x, ⌊K⌋))` and `sum(selects(x, ⌊counter(0, 1, 100)⌋))`
  with `K == counter(0, 1, 100)` are not found equal, since definitions are
  followed in matching only (`Context.↑`), and a side condition
  `ks == ⌊counter(0, 1, m + 1)⌋` with `ks := ⌊K⌋` is not decided (see
  [mapsum1.dfy](benchmarks/sv-comp/dafny/array-crafted/mapsum1.dfy)).
- The branches of a conditional formula are not simplified under the facts
  of the context: `r != 0 ==> if a then 1 == r else 0 == r` stays, while
  `r != 0 && 0 == r ==> p` is closed; nor is a disjunction among the
  hypotheses, `(a && 1 == r || !a && 0 == r) && r != 0` (see
  [standard_password_ground.dfy](benchmarks/sv-comp/dafny/array-examples/standard_password_ground.dfy)).
- Reads over writes at a different position are decided in the neutral
  context (`Simplify.select` with `ctx.neutral`), without the facts: `j != 3`
  among the hypotheses does not reduce `a[3 := w][j]` to `a[j]`; a lemma
  `if j != i then a[i := v][j] == a[j]`, whose side condition is decided
  against the facts, does (see
  [single_elem_safe.dfy](benchmarks/sv-comp/dafny/array-lopstr16/single_elem_safe.dfy)).
- Conditionals inside equations and products are not lifted, e.g.
  `(if c then x else n) == (if c then x * x else n)`; a lemma for equations of
  conditionals with the same test applies, but one for the product
  `(if c then x else y) * (if c then x else y)` does not match, presumably
  since products of conditionals are monomials of the polynomial (see
  [motivex.dfy](benchmarks/sv-comp/dafny/array-lopstr16/motivex.dfy)).
- Facts with coefficients are not combined: `n₁₄ <= 200000` and
  `100000 < n₆` do not give `n₁₄ < 2 * n₆`, since difference constraints
  have unit coefficients; nor is an interval `100000 < n₆ < 100002` on Int
  narrowed to `n₆ == 100001` (see
  [array_doub_access_init_const.dfy](benchmarks/sv-comp/dafny/array-cav19/array_doub_access_init_const.dfy)).
- A pattern sum of a rule variable and a bound variable, e.g. the position
  `c - k` of a store in an update, matches only if the variable takes a single
  summand: `S + -k` matches, `2 * S + -k + -1` and `S + -k + -1` do not, nor
  does the pattern `c - 1 - k` (see
  [array_tiling_tcpy.dfy](benchmarks/sv-comp/dafny/array-cav19/array_tiling_tcpy.dfy)).
- A lemma for a monomial with a coefficient, e.g.
  `2 * ((-x + x * x) / 2) == -x + x * x`, does not match that monomial inside
  an equation, `n * n == 2 * ((-n + n * n) / 2) + n`, presumably since
  equations are normalized as differences of polynomials (see
  [ps2-ll.dfy](benchmarks/sv-comp/dafny/nla-digbench/ps2-ll.dfy)).
- Conjunctions are matched in order, not modulo commutativity: a pattern `R && A && B ==> C`, with a variable `R`
  for the other premises, matches `u < 3 && A && B ==> C`, but neither `A && u < 3 && B ==> C`, nor
  `A && B && u < 3 ==> C`, nor `u < 3 && B && A ==> C`; further variables between them, `R1 && A && R2 && B && R3`,
  do not help. Lemmas that need two premises of a goal therefore depend on the order in which the simplifier
  emits them (see [seq-3.dfy](benchmarks/sv-comp/dafny/loop-invgen/seq-3.dfy), where the order fits). Chains of comparisons are
  conjunctions already (the parser resolves them), only printed as chains. Premises are looked up at any position
  as side conditions instead (`Rewrite.conditions`), also comparisons, e.g. `requires 2 * a + p <= b + 2 * c &&
  c < a` with `ensures (p + 1 < b) <==> true`, as in MADWiFi-encode_ie_ok; this form does not work for seq-3,
  whose rule `0 < a + b` also matches a single summand and decides its side condition by itself.
- No integer rounding: `2 * n <= 2 * k + 1` does not give `n <= k`; no
  cancellation of a factor, e.g. `k * j < 1000000 * k`, and a lemma
  `if 0 <= k then (k * a < k * b) <==> (0 < k && a < b)` does not match it,
  since a variable of a pattern does not match the coefficient 1000000 of the
  monomial `1000000 * k` (see [count_by_k.dfy](benchmarks/sv-comp/dafny/loop-new/count_by_k.dfy)).

## Performance

Measured on binary search and on the SV-COMP examples
(`benchmarks/sv-comp/dafny`):

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
  pattern with all rules, e.g. `X == trace(...)`.
- Matching an equation tries both orders. With the definition of a variable
  (`Context.↑`), `X == trace(...)` matches `Lo == trace(...)` twice, the
  second time with `X` bound to the trace.
- Each round of the fixpoint of `Simplify.apply` simplifies the whole
  formula again. Programs with many loops grow accordingly, e.g.
  [standard_copy9_ground-2.dfy](benchmarks/sv-comp/dafny/array-examples/standard_copy9_ground-2.dfy)
  takes about 20 s for a chain of nine copies, against about 2 s for one copy.
- Non-termination is detected by the budget of steps or by a stack overflow,
  after 8 to 13 s, both reported as "rewriting does not terminate"
  (`Rewrite.apply`, `Simplify.simplify` in both engines), e.g. on counts over prefixes (see bugs.md).
  The symbolic execution of `-teq` is exponential in sequences of conditionals
  and overflows at ten (see bugs.md).

## Deduction engine (`-prove`, package `prove`)

- The record of the implementation, with the open steps, is
  [doc/prove.md](doc/prove.md); the design in
  [doc/prove.md](doc/prove.md).
- The simplex is rebuilt from the constraints of the context at every check that is not cached
  (`Linear.checks`, by the set of constraints); an incremental tableau per context would avoid the rebuilds.
- Closed conditions with binders are looked up modulo the classes of their closed subterms and the renaming of
  their bound variables (`Rewrite.known`), not modulo the arithmetic or the unused dependencies of a fact. The
  instance is simplified before the lookup, which drops its unused dependencies and merges equal ones, while the facts
  keep theirs: the constraints of nested loops carry the counter of the iterations unused
  (`invs(for ⌊K⌋, ⌊counter(0, 1, n)⌋, N? check k, i, nn :: ...)`), so the induction of
  examples/dafny/algorithms/selection_sort.dfy matches them with open lists identified by equations (Oct 14, 2026).
- A side condition that contains a trace as a term is instantiated with fresh bound variables at every evaluation, so
  the views of that trace are recomputed and never memoized (the views are memoized by the marker): a lemma about a
  cycle with `n <= current(trace(...)).0` as a condition did not terminate. Lemmas name the trace by a rule variable
  with an open equation and read its components by open variables (gnome_sort.dfy, merge.dfy); a closed read
  `current(Sv).0` is replaced by its view before the lookup and not found. The insertion sorts and first_duplicate,
  whose constraints contain the inner and outer traces as terms, are blocked by this (doc/array-algorithms, Section
  on the open algorithms).
- The matcher has no case for quantifiers: a rule whose left-hand side is `exists k :: ...` never applies, so an
  existential postcondition needs a witness from elsewhere (examples/dafny/algorithms/max_element.dfy).
- Only variables have definitions in the matcher (`Context.defs`): a term matched by a member of its class that
  contains it cycles (`a[k]` by `S.2[k] == a[k]`); a class member that does not contain the term would be safe to
  try and is not tried yet.
- The C frontend under `-teq` (partitioned by components since Oct 13, 2026) is tested by examples/c/teq and examples/c/verify
  only.
- The matcher of `-prove` matches sums modulo associativity and commutativity, products not: a pattern `m * k`
  does not match the normal form `k * m` (e.g. `div_quotient_remainder`, left in legacy/teq.dfy).
- `-prove` simplifies assertions and function definitions only; programs and attributes pass through unchanged
  (dropped with the former simplifier, Oct 23, 2026; derivatives are computed).
- What `-prove` does not do yet that the former simplifier did (examples/smtlib/prove, test/prove/Simplify.scala):
  - an equation `x == y` of a bound and a free variable is not eliminated by the one-point rule when the bound one
    is the canonical variable of the class (the smallest by name): `forall x :: x == y ==> p(x)` stays,
    `exists x :: x == y && p(x)` too (binders.smt2, `OnePoint.used`);
  - a bound variable defined by an arithmetic equation is not eliminated, e.g. `x` of `y == x + 1` (normalize.smt2);
  - the range `0 <= e % k < k` of a remainder by a literal is not known to the simplex (`range` of
    examples/dafny/prove/remainders.dfy).

## Traces with several accumulators (branch `accumulators`)

- The frontends and printers of Dafny, Boogie, SMT-LIB and SV-LIB, the Lean printer and `-fallback` know traces with
  several accumulators and the component reads (doc/teq.md, Syntax). The matcher of `-prove` matches patterns of several accumulators
  against cycles as a whole (the bisection of examples/dafny/algorithms/bsearch.dfy).
- `-fallback` on lists of traces of several accumulators (an inner loop with a cycle) is implemented (one length
  function for all components) but has no test yet.
- The grammars of Dafny and Boogie need each initial value of a trace to end with a comma before `for`, since a
  comma-separated list commits to a further expression after its separator.

## Trace equation systems (`-teq`)

- The algorithms of examples/dafny/algorithms (Oct 16, 2026): 27 of 30 verified with `-teq -prove`, with lemmas for
  the closed form: summaries of inner loops as plain rules or folds (the passes of the insertion sorts, the scan of
  first_duplicate, the columns of transpose), inductions over the outer trace with the choice of the numbers of inner
  iterations and the constraints of the pass among their side conditions, rules over whole cycles (the partitions,
  whose regions are rules on the atoms over the whole trace of (b, i, j), since a summary of the array component with
  its positions as a counter is not matched), the exit as it stands among the facts (reverse). Open: max_element (no
  quantified left-hand sides), cocktail_sort and counting_sort (step budget); details in doc/array-algorithms.
- `integer_eq` of teq.dfy rewrites `integer(n) == x` into `n == natural(x)` under `0 <= x`, and the result no longer
  states `0 <= x`, which is lost when it followed from the equation itself (reverse.dfy needs it for the conditions of
  its reversal lemma); the unconditional `integer(n) == x <==> 0 <= x && n == natural(x)` keeps it (a change of the
  database with its Lean proof and expected outputs).
- The read relation of the partition into components takes the guards of a guarded body for every result, so a
  counter whose cases are equal (`j + 1` in both) joins the cycle of the variables that the guard reads (the
  partitions); merging equal cases first, or taking the guards only for the results that differ, would keep it out.

- `-fallback`: the fresh functions that generalize terms of type `Nat` (`Fallback.general`, e.g. `indexof(x, xs)` or
  functions of the input over naturals) are declared over `Int` without the fact that their values are nonnegative,
  unlike the entries of lists of naturals and the length functions, which get `0 <= f(xs)` among the definitions of
  the goal; the lowered goal is weaker than necessary. Fix: `general` adds `forall xs. 0 <= f(xs)` for a term of type
  `Nat`, as `named` does for the lengths.
- The runs of the Dafny translations of SV-COMP (`Dafny.unreach-call.Unbounded`, 2 min, 2026-10-10 16:13 against
  15:25): `array-lopstr16/flag_loopdep_simple` is no longer proved (also not with `-fallback`), not because of
  the merged `mod_two_not_zero`; whether the other lemmas of 9a13ed0f or the eta reduction of 97c533c7 is open;
  `loops/vogal-2` reports rewriting does not terminate (one goal locally) since its table of vowels is filled by a
  loop. `loop-crafted/simple_array_index_value_1-1` was open by `mod_two_not_zero`, which is local again.
- The C programs of the translations (`benchmarks/sv-comp/c`) differ from their Dafny sources in 42 of the 270 rows
  of the databases: 32 have lemmas of their own in the Dafny file, which the C file does not contain (mostly closed
  in Dafny, one goal in C); the other 10 differ by the shape of the program that the C frontend builds, e.g. a block
  around the locals of main (`loop-new/gauss_sum`, `half`, `loops-crafted-1/sumt4`, `array-tiling/revcpyswp2`,
  `skipped`, `skippedu`, `array-crafted/zero_sum_const_m2`, `array-programs/partial_mod_count_limited_1`,
  `array-examples/sanfoundry_02_ground`, `sanfoundry_10_ground`).
- Loops bounded by small constants remain in 10 translations (`loop-lit/bh2017-ex1-poly`, `cggmp2005b`,
  `hh2012-ex3`, `loop-invgen/id_build`, `loop-simple/nested_1b`, `loops/eureka_01-2`, `invert_string-3`,
  `sum04-1`, `sum04-2`, `vogal-2`), some asserting the bound, e.g. `k == 4` after `while k <= 3`.
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
- Facts about terms are not derived by the simplifier (see [doc/prove.md](doc/prove.md#facts-that-the-goal-does-not-mention));
  bsearch.dfy needs a cut, `assert φ; assume φ;`, and `-teq`
  does not assume assertions. `-prove` has forward lemmas (`{:fw}`, see
  [doc/prove.md](doc/prove.md)), with which the binary search of examples/dafny/algorithms/bsearch.dfy closes without the cut;
  which lemmas of the database should be `{:fw}` rather than `{:rw}` is open.
- The simplifier evaluates integer division on literals and divides by
  literals on Real, but knows no bounds of division, e.g. `l <= (h + l) / 2`
  for `l <= h` is a lemma in teq/bsearch.dfy (`-prove` bounds `t div k` in its
  linear arithmetic, not yet `quot` of C, see [doc/prove.md](doc/prove.md)), nor cancels factors,
  e.g. `2 * n / 2` (see
  [mlceu2.dfy](benchmarks/sv-comp/dafny/array-tiling/mlceu2.dfy),
  [array_of_struct_ptr_monotonic.dfy](benchmarks/sv-comp/dafny/array-industry-pattern/array_of_struct_ptr_monotonic.dfy)).
- Solutions of arithmetic equations are inlined into polynomials only
  (`Chains.solved`), not substituted elsewhere, e.g. `forall x. x == y + 1
  ==> p(x)` stays; a solution that depends on its variable through the
  equations of the context is not inlined (`Chains.acyclic`).
- The selection of the dependencies of a pattern is not backtracked when a side condition fails: a lemma whose
  left-hand side binds `ks` to the first matching dependency (`⌊K⌋`) and whose side condition needs the fragment
  whose first dependency is another list (`⌊R⌋`, selected since the initial value `X(k)` matched its bound variable)
  fails, hence the variant `invs_current_counter_other` with an independent first dependency
  (see [nested_mult.dfy](examples/dafny/algorithms/nested_mult.dfy)).
- A bare bound variable on one side of the body of an `invs` pattern is synthesized as a map (`Rewrite.instantiate`):
  `invs(for ks, js check k, j :: n <= j)` matches every comparison fragment and
  `invs(for ks, Ns, js check k, nn, j :: j == integer(nn))` every equation fragment with `integer` of a bound
  variable (`r' == r + integer(nn)`), with `js` a map over the fact's dependencies; as a left-hand side with `invs`
  side conditions both cycle (the exit lemma of the `nested` module, found by pair runs of its lemmas on
  cocktail_sort.dfy, NOTES.md finding 29); a function symbol on the side of the bound variable,
  `invs(for ks, Ns check k, nn :: integer(nn) <= n)`, is specific. `Rule.check` could reject a left-hand side whose
  body has a bare bound variable of a variable dependency together with an `invs` side condition.
- A bound that is not a difference constraint is not decided from two facts: `len <= 2 * integer(m) + 1` from
  `n <= integer(m) + lo + 1` and `lo == integer(m)` (cocktail_sort.dfy states the bound in the goal's form with `lo`
  an open variable).
- A polymorphic lemma with a higher-order variable in a side condition is not matched: `current_results_steps<a>`
  with `F: (a, int) -> a` (or `F: a -> a`) never fires, the monomorphic lemma does; `X: a -> int` in a side
  condition is matched, so the problem is a higher-order variable of the type parameter's type
  (see [nested_mult.dfy](examples/dafny/algorithms/nested_mult.dfy), [transpose.dfy](examples/dafny/algorithms/transpose.dfy)).
- A literal disjunctive guard `n <= j || i < m && a[i] <= b[j]` in a trace pattern is never matched, while a
  higher-order guard `G(i, j)` is, pinned by a quantified side condition `forall i, j :: G(i, j) <==> ...` that the
  simplifier decides by beta reduction; the same pin serves for every literal pattern that is not matched (`j - 1`
  as a store index, `n - k - 2` as an initial value), see [merge.dfy](examples/dafny/algorithms/merge.dfy),
  [insertion_sort.dfy](examples/dafny/algorithms/insertion_sort.dfy), [cocktail_sort.dfy](examples/dafny/algorithms/cocktail_sort.dfy).
- A higher-order variable for an array read, `G(i)` against `a[i]`, is instantiated by the array itself, and the
  right-hand side then contains `a(i)`, which no lemma matches
  (see [prefix_sums.dfy](examples/dafny/algorithms/prefix_sums.dfy), which reads the array literally instead).
- A variable argument of an uninterpreted function is not expanded by its definition when a pattern is matched
  below it: `sorted(c, 0, n)` with `c == current(C)` is not matched by a left-hand side `current(trace(...))`, but
  the whole atom `sorted(current(trace(...)), 0, s)` is, likewise `selects(current(...), ...)` with `selects` as
  the head inside `count`; the length must then be a variable `s` with `s == m + n` as a side condition, since a
  pattern `m + n` of two variables is not matched (see [merge.dfy](examples/dafny/algorithms/merge.dfy)).
- A closed side condition that equates a list with a trace, `is == ⌊trace(0, for ⌊counter(0, 1, nn)⌋, js do ...)⌋`,
  is decided by the simplifier and fails, since `⌊I⌋` is not expanded; the same with an open trace variable,
  `Iv == trace(...)` matched against the hypothesis `I == trace(...)` and then `is == ⌊Iv⌋`, works, also for
  `Iv == counter(0, 1, n)` (see [merge.dfy](examples/dafny/algorithms/merge.dfy), [counting_sort.dfy](examples/dafny/algorithms/counting_sort.dfy)).
- A quantified hypothesis `forall i :: 0 <= i < n ==> 0 <= a[i] < k` is matched by no side condition, open or
  closed; the specification states it as an atom `keys_below(a, n, k)` instead
  (see [counting_sort.dfy](examples/dafny/algorithms/counting_sort.dfy)).
- Arithmetic premises of a quantified side condition are substituted before the step lemmas see it: `i == k + 1` in
  `forall b, k, i :: ... && i == k + 1 && ... ==> sorted(F(b, k, i), 0, i + 1)` turns the conclusion into
  `sorted(insert(b, k + 1), 0, k + 2)`, which the pattern `sorted(insert(b, i), 0, i + 1)` does not match
  (see [insertion_sort2.dfy](examples/dafny/algorithms/insertion_sort2.dfy), whose induction drops the premise).
- Higher-order patterns (`Rewrite`) take distinct bound variables or terms
  instantiated already as arguments; other arguments match only if an
  earlier occurrence instantiated the variable, and a single bound variable
  of the pattern cannot abstract several of the expression (no tuples).
  Terms are abstracted at all of their occurrences.
- Lemmas whose left-hand side is an `invs` with a bare comparison or equation as the body and a dependency that
  is a variable, e.g. `above_iterations_def` (`k < t`), match every fragment with such a body, with the dependency
  synthesized as a map: a resolved constraint `k + 1 + integer(nn) <= n` of an inner loop is consumed as
  `above_iterations(n, maps(... n - integer(nn)))`, and an atom for the exit of a pass,
  `invs(for ks, js check k, j :: n <= j + k + 1) <==> exits(ks, js, n)`, matches `2 k + 1 < n` and `0 <= integer(nn)`
  (see [cocktail_sort.dfy](examples/dafny/algorithms/cocktail_sort.dfy), [selection_sort.dfy](examples/dafny/algorithms/selection_sort.dfy),
  which keeps the raw constraint as a side condition). Such definition lemmas should have a body that the matcher
  cannot synthesize, e.g. an `earlier` read as in `agree_prefix_def`.
- The candidates for the database among the lemmas of examples/dafny/algorithms are in
  [ideas/database-review.md](ideas/database-review.md) (Oct 23, 2026); the fragment lemmas of
  [fragments.dfy](examples/dafny/algorithms/fragments.dfy), once candidates for teq.dfy, are obsolete since `-teq`
  closes nested loops and the module `nested` is retired: the nested examples verify with the database alone;
  `current_trace_histogram` is in aggregation.dfy.
- Induction lemmas with the invariant as a predicate indexed by the iteration, `bubbled(b, k, len)`, and a
  quantified side condition `forall b, k :: 0 <= k < integer(m) && I(b, k) ==> I(F(b, k), k + 1)` that the simplifier
  decides by step lemmas on atoms, replace whole-loop lemmas of sorting algorithms; the number of steps must be
  constrained exactly or the invariant clamped, since steps beyond the range are unconstrained otherwise
  (see [bubble_sort.dfy](examples/dafny/algorithms/bubble_sort.dfy), [selection_sort.dfy](examples/dafny/algorithms/selection_sort.dfy)).
- No instantiation of the iteration constraint at a witness, e.g. a search
  whose constraint states that `P` holds before the exit `n`, and `!P(j)`,
  which gives `n <= j`; the examples abstract the constraint by an atom first,
  e.g. `!occurs(e, selects(a, ⌊counter(0, 1, n)⌋))` by `not_occurs_selects` of teq.dfy, which a second lemma
  takes as its side condition (see
  [standard_sentinel-2.dfy](benchmarks/sv-comp/dafny/array-examples/standard_sentinel-2.dfy)),
  since a side condition that is an iteration constraint does not terminate.
- Nested loops: the outer trace takes the values of summarized inner traces,
  whose composition, e.g. `k == n * m`, is not accelerated (see
  [nested-1.dfy](benchmarks/sv-comp/dafny/loop-new/nested-1.dfy)).

## Dafny frontend

- Containers: missing comprehensions, `multiset(s)`, the multiset update
  `m[x := n]`, `>=` and `>`, disjointness `!!`, `seq(n, f)`, and
  multi-dimensional updates.
- `x.f` and `x.C?` on variables only, e.g. `P(1).a` is "member access on an
  expression that is not a variable". The qualified name `T_f` comes from the
  declared sort of the variable, before type checking. Members inside
  `type`/`datatype` bodies need no `this.` (`dafny.Parser.isMember`), although
  [examples/datastructures/stack.dfy](examples/datastructures/stack.dfy) still
  writes it. Plan:
  1. testers `e.C?` on terms: the constructor determines the datatype
     (`state.exprs.is`), drop the restriction to variables;
  2. functions and selectors on terms: the parser emits a generic
     application `.f` with fresh types and the receiver first, `Type.check`
     records it as pending, and `Overload.resolve` looks up `T_f` in
     `state.funs` by the sort of the receiver, extending `impl` by a lookup
     in the state; a receiver whose type is still a parameter is an error;
  3. method calls on terms (`y := f(x).m()`) need the receiver's sort when
     the statement is built: type check the receiver on its own, otherwise
     keep the restriction; last;
  4. tests: [stack.dfy](examples/datastructures/stack.dfy) without `this.`, nested
     accesses `f(x).g()`, errors for unknown receivers.
- `var` declarations before statements; contract clauses in the fixed order
  `modifies`, `requires`, `ensures`, `assumes`, `commits`, `decreases`, for
  loops `modifies`, `invariant`, `decreases`.
- Names that are neither identifiers nor operators, e.g. the instances
  `f<Int>` of `-monomorph`, are escaped by backticks, which the scanner reads
  back but Dafny does not have; names containing backticks are not handled.
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

- Integers are unbounded, signed overflow is not modelled; arrays are
  values, sizes are ignored. Expressions have the integer types of C
  (`c.IntType`: signedness and rank, sizes by `-arch`), with the integer
  promotions and the usual arithmetic conversions (`c.Parser.common`).
- Unsigned integers wrap around: the results of `+`, `-`, `*`, and `<<` in
  an unsigned type, and conversions of values to one (assignments,
  arguments, returns, casts, operands of a common unsigned type, e.g.
  `-1 < 1u` is false) apply the overflow function of its size, `uchar`,
  `ushort`, `uint`, `ulonglong` of the prelude (`x mod 2^n`, rw), unless the
  value fits (`c.Parser.convert`); the printer prints them as casts.
  Unsigned loop counters, `x = uint(x + 1)`, are no counters for `-teq`,
  which does not accelerate them (see `examples/c/teq/from.c`, run with
  `-unbounded`).
- The values of `__VERIFIER_nondet_<type>()` are within the range of their
  type, for `char`, `short`, `int`, `long`, `longlong`, their unsigned
  versions, and `size_t` (`c.Parser.havoc`). Variables declared without a
  value are arbitrary integers.
- `-unbounded`: neither ranges nor overflow, only the values of unsigned
  nondeterministic functions are nonnegative, as before.
- `goto` only to a label whose statement does not fall through (e.g.
  `END: return 0;`, `ERROR: { reach_error(); abort(); }`), which is copied in
  its place, or to itself (a loop without exit); other gotos, e.g. those of
  state machines, are not supported (`c.Parser.goto`); open: gotos to a label
  whose statement falls through, by copying the statements.
- `sizeof` of an expression by the declared integer type and array sizes of
  its variable (`c.Parser.bytes`), otherwise by its type.
- No structs, floating point, bitwise operators, preprocessor; pointers
  only as arrays allocated by `malloc`, `alloca`, `calloc` (see [SV-COMP.md](SV-COMP.md)), and otherwise as values of `Ptr`
  in the prelude of C ([prelude.bpl](resources/cuvee/c/prelude.bpl)), which
  are compared but not dereferenced; no `&`, `*p`, or pointer arithmetic.
- The modifies clause of a loop is inferred from the core program, where a
  local variable that shadows a global one of the same type counts as global.
- ACSL annotations (0.38.0, `/*@ ... */` and `//@`): function contracts
  `requires`, `ensures` (`\result`, `\old`), `decreases`; `loop invariant`,
  `loop variant` before `while`, `for`, `do`; `assert`; terms with `==>`,
  `<==>`, `\forall`/`\exists` (variables of C types range over the type,
  except with `-unbounded`, `integer` and `boolean` unbounded), chained
  comparisons, mathematical arithmetic without wrap-around, casts as in C.
  `assigns` and `loop assigns` are the modifies clauses of their functions
  and loops (their identifiers, the global ones; locals are inferred), which
  the body must respect, except with `-teq` and `-chc`, which infer the
  modifies clauses (0.41.5; before, the clauses were skipped). `\at(e, L)` for `Pre`, `Here`, `LoopEntry`, `\valid` and
  `\valid_read` (true), ranges of unsigned parameters of functions with
  annotations as preconditions as in Frama-C/WP (those of the unsigned
  variables that loops modify are no implicit invariants since 0.41.6), and
  `&`, `|`, `^` of truth values (0.39.3). Global declarations (0.40.0):
  `axiomatic Name { ... }`, whose name is dropped (it groups, it does not
  scope), and the same declarations outside of one: `logic T f(params)` and
  `predicate p(params)`, uninterpreted or `= body` (also recursive), with
  `reads` skipped, as `DeclareFun`/`DefineFun`; `axiom name: phi;` as
  `Assert(Axiom)`, `lemma name: phi;` as `Assert(Lemma)` with `:free`
  (trusted, inductive lemmas are beyond z3), both `:named`; calls of logic
  functions in terms; pointers in logic signatures and quantifiers are
  arrays (`int *a`, `int **m`); logic declarations cannot refer to program
  variables (pass them as parameters). Not supported: other `\...`
  constructs (`\separated`, other labels, ...), labels of lemmas
  (`lemma l{L1, L2}`, state them over two arrays), behaviors, ghost code,
  calls of C functions in annotations; contracts of `main` are conjoined
  with the zero values of the globals. The printer writes contracts, loop
  invariants and variants, and assertions that are not C (quantifiers,
  implications, `\old`, calls of logic functions) as ACSL, and functions
  (`DeclareFun`, `DefineFun`), axioms and named lemmas as global ACSL
  declarations. Step axioms of recursive definitions are best stated
  backwards, `n > 0 ==> f(a, n) == f(a, n-1) + a[n-1]`: z3 cannot trigger on
  `f(a, n+1)` (`+` is interpreted) and unfolds `f(a, n)` forever.
- ACSL on SV-COMP ([benchmarks/acsl](benchmarks/acsl), the tasks of the categories Arrays and Loops with
  hand-written annotations, checked with `-vcgen -z3`; results per folder and the causes of the open tasks in
  [benchmarks/acsl/README.md](benchmarks/acsl/README.md)); open issues of the support, by impact:
  - A refuted goal is printed as one SMT-LIB string, `(error "goal does not
    hold" "Sat" "(forall ...)")`, without the annotation (loop invariant,
    assertion, postcondition, line) that failed; `-vcgen -z3` prints
    nothing when all goals hold.
  - The C operators `shl`, `shr`, `bitand`, `bitor`, `bitxor`, `bitnot` are uninterpreted (`:abstract` in the C
    prelude, so a refutation through them is `unknown`): interpret them where possible (shifts
    of constants as multiplications by powers of 2, masks of low bits as `%`, e.g. `(x & 5) == 5` with
    `x % 8 == 5` of `bin-suffix-5`); `&` of two truth values is `and` already (`c.Parser.logical`).
  - Contracts of functions that read globals need the globals' values as
    preconditions (`loops/eureka_05`, `requires n == 5`), as in Frama-C; a
    contract on `main` is the only one that sees the initial values.
  - `\min`, `\max`, `\abs` are not supported (the scanner rejects them);
    `array-programs/partial_mod_count_limited_*` write `\min(a, b)` as the
    conditional `(a <= b ? a : b)` instead.
  - Labels of `\at` other than `Pre`, `Here`, `LoopEntry`.
  - `-chc` answers `unknown` on the unsigned arithmetic modulo 2^n of annotated programs
    ([acsl_ranges.c](examples/c/vcgen/acsl_ranges.c) is checked with `-vcgen` only).
  - Z3 answers `Unknown` on nonlinear closed forms: `nla-digbench/geo*`
    modulo 2^64, `lcm2`, `prod4br`; `array-programs/partial_mod_count_2-5`
    (counts with integer division); `array-patterns/array26` (parity of a
    count).
  - `nla-digbench/prodbin-ll` and `geo2-ll_unwindbound1` time out since 0.41.4, which they did not with 0.40.0
    (2 to 3 s), also without `-verify` (not bisected).
  - Runs under CPU load time out at 10 s on trivial tasks (`loop-lit/mine2017-ex4.6`
    proves in 2.6 s alone); the limits of the runs in the README are not
    those of the tool.
  - Deferred: array parameters that a function assigns as in/out parameters. Arrays are values in Cuvée's C
    and ACSL, so `void incrementArray(int src[N], int dst[N])` assigns a copy of `dst`: its `ensures dst[t] ==
    src[t] + 1` speaks of the value passed in (z3 answers `Unknown`, quantified), and the caller's `dst` stays
    unchanged after the call, while C passes a pointer (wrong false verdicts, see bugs.md; the three ACSL tasks
    affected, `array-examples/sanfoundry_43_ground` and `data_structures_set_multi_proc_*`, take their arrays as
    global variables since Oct 14, 2026). In/out parameters, whose final value the caller receives and
    `ensures` refers to, are sound when the arguments do not alias, which `\separated` states in Frama-C and
    distinct variables as arguments would ensure here. The memory clauses of the annotations are removed
    (`\valid`, `\valid_read`, `\separated`, `\null`); the two tasks with
    `\null` (`array-industry-pattern/array_ptr_partial_init`, `array-lopstr16/partial_lesser_bound`) end in
    "arrays of pointers are not supported".
- z3 answers `unknown` for Horn clauses with division by variables
  ([examples/c/vcgen/div.c](examples/c/vcgen/div.c)), and for calls in loops whose
  callee has no goals, since its precondition is inferred from the calls
  (only the entry point has a precondition of its own, see `-entry`).
- Errors of the C frontend on SV-COMP (Arrays and Loops, 0.34.22, 101 tasks;
  with 0.35.2, 3 parse: `loops/compact`, `heavy-1`, `heavy-2` by `sizeof` of
  expressions), besides `goto` to labels that fall through (26, see above;
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
  - `*p` in `p <= tmp` with pointers is "not an integer"
    (`loops/verisec_NetBSD-libc_loop`, `veris.c_NetBSD-libc_loop`); `&x` and
    `*p` otherwise report "not supported".
  - Arrays of pointers are not supported (`array-industry-pattern/array_ptr_partial_init`,
    `array-lopstr16/partial_lesser_bound`).
  - GCC builtins are unknown functions, e.g. `__builtin_bswap32`
    (`array-examples/relax-2-2`).

## Portfolio of TEQ and CHC (SV-COMP)

The configurations complement each other: in the runs of Oct 11, 2026 on
ReachSafety-Loops, `-chc -z3` (1 min, `xml/cuvee-chc.xml`) proves 146 tasks
and `-teq` (2 min) 123, together 195; on ReachSafety-Arrays 8 and 133,
together 137. Only `-chc` reports violations (85 correct, none wrong), since
`unsat` of the Horn clauses is a counterexample, whereas a model of Z3 for a
goal of `-fallback` is none (the encoding abstracts the goal, `cuvee.py`
scores it unknown).

- A portfolio in Cuvée, e.g. an option that `cuvee.py` passes with the time
  limit (BenchExec's rlimits): the steps in sequence, not in parallel, since
  BenchExec counts the CPU time of all cores against one limit, e.g. `-teq`
  for a short slice (usually fast or stuck), then `-chc` for most of the
  remaining time, then `-fallback` with the rest; the slices from the CPU
  times of the 15-minute runs; parsing shared between the steps.
- Disagreement is unknown: a proof by `-teq` and `unsat` by `-chc` indicate
  a bug in one of them, and wrong results cost 32 (true) and 16 (false).

## SV-COMP task definitions

- The properties and expected verdicts of a task (`Task.properties`) are read
  but not used; only a single input file is supported, in a language that
  Cuvée reads, by its extension (`yml.Source.lang`).
- The C versions of the local benchmarks (`benchmarks/sv-comp/c`) are patched
  by nondet.py, sizes.py, and bounds or conditions on the inputs of 34 tasks
  (see [false-verdicts.md](benchmarks/sv-comp/c/false-verdicts.md)); open:
  - not checked by a full run: of the patched tasks, 10 of group 2 have not
    run again (eureka_01-2, array_init_nondet_vars,
    array_min_and_copy_shift_sum_add, mono-crafted_6,
    linear-inequality-inv-a, -c, -d, hard-ll, underapprox_1-2, mod3) and 23
    of group 3; the wrong true verdicts of Symbiotic (57) and AISE (55),
    nearly all in files with uninitialized locals, should be gone with
    nondet.py; Cuvée has not run on the patched files.
  - 9 tasks that only AISE finds false, without a known cause (group 4:
    bAnd5, bor5, xor5, mapsum5, mapavg5, sanfoundry_10_ground, init-2-n-u,
    gj2007, mono-crafted_1); AISE's first stage fails (`bin/runexec`
    missing), so these verdicts come from its KLEE fallback.
  - The Dafny translations lack the patches
    ([c_patches.diff](benchmarks/sv-comp/dafny/c_patches.diff)); printing the
    C versions again undoes them. The expected verdict true of the group 1
    translations is wrong without their conditions.
  - partial_mod_count_limited_gen assumes `N % 60 == 0`, which suffices but
    is stronger than needed.
  - geo1-u is unsafe only by the wrap-around of `unsigned long long`, which
    Cuvée+Z3 and Korn prove safe (see bugs.md).
  - 5 translations lose an update of an array parameter and are excluded
    from the task sets until fixed (see the
    [README](benchmarks/sv-comp/c/README.md)).

## Bitvectors

`BitVec(n)` with the SMT-LIB literals and functions (`BitVecs`). Open: no
simplifier rules; widths cannot be parameters.

- Dafny: no `<<`, `>>` (as a token, `>>` would close nested type arguments
  `seq<seq<int>>`), no infix `|` (which clashes with `|s|`), no
  `RotateLeft/Right`, no `bv0`; `x as int < n` parses `int<` as type
  arguments, it needs parentheses.
- Boogie proposal: types `bv8`, literals `5bv8`, `x ++ y`, `x[8:0]` (exclusive
  upper bound), and functions declared with `{:bvbuiltin "bvadd"}` resolved to
  the instance of `BitVecs.fun`.

## Parallel composition

- `Horn` rejects `parallel` and ignores assumptions and commitments.
- Only calls can be composed.
