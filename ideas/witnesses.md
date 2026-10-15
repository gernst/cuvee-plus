# Verification witnesses for SV-COMP

Cuvée writes no witnesses (`GetWitness` is answered `unsupported`, [Cmd.scala](../src/cuvee/core/Cmd.scala)).
SV-COMP scores a correct verdict without a confirmed witness with 0, but a wrong one with −32 (true) or −16
(false): as it is, the verdicts of Cuvée can only cost points. The analysis and the plan of Oct 14, 2026; nothing
is implemented yet.

## The formats

- **C, format 2.0/2.1** (YAML, [sv-witnesses](https://gitlab.com/sosy-lab/benchmarking/sv-witnesses), local copy
  in `~/Tools/sv-witnesses`, `user-guide/Witness-Format.md`):
  - correctness: an `invariant_set` of `loop_invariant` (evaluated before the controlling expression) and
    `location_invariant` entries, each at a file, line, column and function, whose value is a C expression
    (`c_expression`, or `ext_c_expression` with `\at(x, Pre)`); 2.1 adds ghost variables (global scalars,
    updated by C expressions at locations), function contracts and the label `inductive`. The expressions have
    **no quantifiers** and no logic functions.
  - violation: a sequence of segments of waypoints (`assumption`, `branching`, `function_enter`,
    `function_return`), the last one a `target`.
  - An empty correctness witness (`content: []`) is valid: the validator proves the task on its own. Symbiotic
    emits exactly that (`results/symbiotic.*.files/**/witness.yml`).
- **SV-LIB 1.0** (`~/Projects/sv-lib/examples/validation-with-witness`): the witness is part of the language.
  - correctness: a list of `annotate-tag` commands with `:invariant` and `:decreases`, terms of SMT-LIB in the
    logic of the task;
  - violation: `select-trace` with a model of the constants, `init-global-vars`, `entry-proc`, `steps`
    (`init-proc-vars`, and `leap <tag> (x v) ...`, which jumps to a tagged loop in a given state, without
    listing the iterations) and the `incorrect-annotation` that is violated.
  - The C-translated tasks declare `QF_LIA`, so their invariants are presumably quantifier-free; they are loops
    only, without arrays.

## The core problem: TEQ proofs contain no invariants

`-teq` summarizes a loop by trace equations, and `∃ n, K, X. TEQ` is an inductive invariant (theorem 4.7 of the
paper), but its existential ranges over sequences, not over the current state. `-prove` rewrites the goal of the
final state with the database: the result is a derivation, not an invariant. The representation gap that TEQs
avoid comes back with the witnesses.

An invariant follows from the closed forms of the traces at a generic number of iterations `n`:

- the introduction rules name the fragments (`counter`, `stores`, `consts`), the acceleration rules give their
  closed forms, `current(counter(i, c, n)) = i + n·c`, a store loop `∀ j. a[j] = (j < n ? f(j) : a0[j])`;
- `n` is eliminated by the counter, `n = (i − i0) / c`;
- the initial values `x_old` are terms over the values at the entry of the function and the nondeterministic
  values of the symbolic execution (the substitution of `TEQ.Path`); those that cannot be named any more need
  ghost variables assigned before the loop (2.1);
- the iteration constraints (`invs`) become bounds, e.g. `n <= len`.

## Challenges

1. **Quantifiers.** The strength of Cuvée is arrays: 132 to 142 safe tasks of ReachSafety-Arrays, 112 that no
   other tool of the table of [doc/paper](../doc/paper/cuvee.tex) proves. Their invariants are
   `∀ j < i. a[j] == f(j)`, which C expressions cannot state; ghost variables are scalars and cannot replace
   a quantifier. Korn instantiates at the index that the property reads (`A[N-1]`), which needs that index in
   scope at the loop and fails for check loops `for (i...) assert(a[i] == ...)`.
2. **Functions of the database** (`sum`, `count`, `max`, `pow`, `sorted`, `perm`) are recursive and cannot be
   written in C; only closed forms of arithmetic (triangle numbers) can.
3. **Partial facts are not inductive.** Forward lemmas and bounds ("max is at least every element so far") need
   not be inductive alone; a witness need not be `inductive`, but the validator then has to strengthen them.
4. **Nested loops and inlining.** An inner loop is a value of the outer update, so its invariant states the
   progress of the outer loop. `-teq` inlines calls: a loop in a function called at several sites has one
   invariant per site and one location in the witness, hence a disjunction or `\at(x, Pre)`.
5. **Source locations.** The C scanner tracks lines and columns (`%line %column` in
   [Scanner.flex](../src/cuvee/c/Scanner.flex)), the syntax and the core drop them. A witness needs the line and
   column of the loop and of the call of `reach_error()`, the names of the functions, the C names of the
   variables in scope, and the SHA-256 of the `.i` file. The evaluation point of a `for` loop (after the
   initialization and after the increment, before the test) is the head of its translation into `while`;
   `continue` remains to be checked.
6. **C semantics in the expressions.** Signed integers are mathematical integers, the ranges of nondeterministic
   values are dropped (`Config.unbounded`): an invariant such as `s <= i*255` may itself overflow in C and needs
   `(long long)` casts. `div` and `mod` of SMT-LIB round otherwise than `/` and `%` of C (a case split, or
   operands known to be nonnegative); `store` terms have no counterpart in C.
7. **Violation witnesses.** `Prove.counterexample` gives values of at most four variables of a remaining goal,
   which must be traced back to their nondeterministic calls (the numbers of iterations are dropped). All
   `__VERIFIER_assert` share one `reach_error()`, so the target needs a `function_enter` waypoint at the
   assertion, hence a map from goals (also after `-split`) to source assertions. A counterexample that depends
   on an overflow is undefined behavior, which invalidates the witness, and the verdict.
8. **The logic of SV-LIB tasks** (`QF_LIA`) presumably excludes quantified invariants.

## What the validators prove alone

Cuvée's runs of Oct 13, 2026 (`results/cuvee.2026-10-13_22-11-17`, `-21`) against the official results of
SV-COMP 2026 of CPAchecker and UAutomizer, which are also validators, as an estimate of what an empty witness
gets confirmed:

| | Cuvée correct | also confirmed by CPAchecker or UAutomizer |
|---|---|---|
| Arrays true | 138 | 5 |
| Arrays false | 9 | 0 |
| Loops true | 149 | 119 |
| Loops false | 16 | 7 |

An empty witness recovers most of Loops and almost nothing of Arrays, where the witness has to carry the proof.

## Plan, cheapest first

1. **Infrastructure and trivial witnesses.** Implemented (Oct 14, 2026): `-witness <file>`, which implies
   `-verify`, writes for the answer to a C program or to a task whose input is C (`yml.Witness`, the sink wrapper
   `Witnessing`, written with SnakeYAML Engine, unit tests `test.yml.Witnesses`, since tests write no files and the
   uuid and the time are fresh): format 2.0, the input file as given on the command line or relative to the task,
   its SHA-256, the data model of `-arch` or of the task, the specification `G ! call(reach_error())` (the only
   property that `-verify` decides for C; `cuvee.py` passes the C file, not the task or the property file), all
   strings quoted (PyYAML took the creation time for a date), the numbers plain (`Quoting`). An `invariant_set`
   without invariants for true; for false a `violation_sequence` with a single segment, the target at the call of
   `reach_error` or `__VERIFIER_error` (Oct 15, 2026), whose names the C scanner locates (`Token.Located` of a value),
   found by a scan of the input (`Witness.targets`: followed by `(`, not preceded by `void`, i.e. no declaration or
   definition, and not in a string); none if the program has no call or several, since the failing assertion is not
   known: of the 1430 tasks of Arrays, Loops and VerifyThis-Loops, 1345 have exactly one call, 16 several, 69 none
   (a regular expression over the sources). For a while both witnesses were empty, the violation witness without
   segments, which passes the linter but lacks the final segment that the format requires. `-witness witness.yml` is in `xml/cuvee*.xml` (Oct 15, 2026). Open: fm-tools, and the measurement with the
   validator definitions of svcomp-bench-defs (`validate-correctness-witnesses-2.0`,
   `validate-violation-witnesses-2.0`); expected about 120 confirmed results of Loops.
2. **Invariants of `-chc`.** The model of Z3 gives the predicates of the loop heads. In SV-LIB nearly for free:
   the model is SMT-LIB already, its arguments are renamed to the variables in scope at the tag, the values at the
   entry become `(at x tag)`, and `get-witness` prints the `annotate-tag` commands. In C the same with the
   translation of challenge 6. The derivation of `unsat` gives the nondeterministic values of a violation, as
   assumption waypoints.
3. **Invariants of TEQ for scalar loops.** The construction above for counters, polynomial closed forms
   (nla-digbench) and bounds, checked by Cuvée itself: printed as ACSL loop invariants (the C printer prints
   `\forall`) and run with `-vcgen -z3`, as for [benchmarks/acsl](../benchmarks/acsl); only invariants that
   pass are emitted, which also catches wrong verdicts. Violations in SV-LIB suit TEQ: `leap` reaches the state
   after `n` iterations without the iterations.
4. **Quantified invariants for arrays**, a question of the format first: propose a keyword `\forall` for
   `ext_c_expression` (its keywords are designed for extension) or invariants in ACSL (which Ultimate reads), to
   the community of SV-COMP, with the 112 unique proofs as the case. Meanwhile, instantiation at the indices that
   the property reads, where they are in scope.
5. **Scoring.** A true without a confirmed witness gives 0 and risks −32: in a competition configuration, answer
   true only with a witness that checks. The run of CTranslated of Oct 14, 2026 has one wrong true that this
   would have caught.

## Source positions in the C frontend

Witnesses need the line, the column (1 is the first character, a tab counts as 1) and the function of the loops
(`loop_invariant`), of the call of `reach_error()` (`target`), and later of the assertions, the nondeterministic
calls and the branches; empty witnesses need none, SV-LIB has its tags. The scanner counts lines and columns
(`%line %column` in [Scanner.flex](../src/cuvee/c/Scanner.flex)), which no token keeps. The plan (Oct 14, 2026)
touches only `easyparse` and `cuvee.c`: a token kind of its own for the keywords whose location a witness names,
which the grammar reads like a keyword, and the attribute `:location` of the loops of the core. Layers 1 to 5 are
implemented (Oct 14, 2026, not committed); the writer of the witnesses is not.

1. **Tokens** ([Input.scala](../src/easyparse/Input.scala)): a third case of `Token`,
   `case class Located(name: String, text: String, line: Int, column: Int)`, a keyword whose text is its name, or
   since Oct 15, 2026 also a value (the names of the error functions). `Keyword` and `Value` are
   unchanged, so are their constructions (the `Syntax.apply` of all frontends, `sexpr`, `Token.eof`) and the
   matches by name that do not concern these keywords: `Balanced` and `Until` of the C grammar (brackets, braces,
   `;`), the matches of Typedefs (`typedef`, braces, `;`), `takeWhile(_ != Token.eof)`. No code outside the two
   packages matches the kinds of tokens.
2. **easyparse** ([Scanner.scala](../src/easyparse/Scanner.scala), [Parser.scala](../src/easyparse/Parser.scala)):
   `Scanner.Match`, the only match of keywords by name, accepts both,
   ``case (Token.Keyword(`name`) | Token.Located(`name`, _, _), in_) => in_``, so `S("while")` and every grammar
   that uses the keyword stay as they are (the `while` of a `do`); `L(name): Parser[(Int, Int)]`, like `T(name)`
   for values, takes a `Located(name, ...)` and returns its line and column (`Parser.Locate`).
3. **The scanner** ([Scanner.flex](../src/cuvee/c/Scanner.flex)): `while`, `do` and `for` leave `{kw}` for a rule
   of their own, `"while" | "do" | "for" { return Syntax.located(yytext(), yyline, yycolumn); }`, where
   `c.Syntax.located` builds `Token.Located(name, line + 1, column + 1)` from the 0-based positions of jflex. The
   lines are the physical lines of the `.i` file, which the witnesses name; the `#` directives are skipped and need
   no mapping. Scanner.java is regenerated (`jflex -q --nobak src/cuvee/c/Scanner.flex`). Typedefs needs nothing:
   no type contains these keywords.
4. **The grammar and the syntax** ([Grammar.scala](../src/cuvee/c/Grammar.scala),
   [Syntax.scala](../src/cuvee/c/Syntax.scala)): `L` in place of the keyword,
   `P(L("while") ~ parens(expr) ~ stmt).map { case at ~ test ~ body => While(test, body)(at) }`, likewise `do` and
   `for`. The loops keep the position in a second parameter list, `case class While(test: Expr, body: Stmt)(val
   at: (Int, Int))`, also `DoWhile`, `For` and `Loop` (which takes the position of its `For`); it is not part of
   equality and of patterns, so the matches of the parser (`indexed`, `reads`, `unlabeled`, `labels`, `acsl`, ...)
   stay as they are, and their companions are no functions any more. Not a wrapper `Located(pos, stmt)` around
   every statement, which breaks the matches that look into statements (the `Case`s of a `switch`,
   `target(stmts.last)`, `reach_error` under a label).
5. **The core** ([Parser.scala](../src/cuvee/c/Parser.scala)): `while_` adds the attribute
   `:location (line column function)` to the core `While`, after `:modifies` and the clauses of ACSL, with the
   name of the function from `Ctx.function`. Its value is an s-expression (`sexpr.Num`, `sexpr.Id`), not a class
   of `cuvee.c`, since the printers of the other languages, which are out of scope, print every attribute: the
   SMT-LIB printer writes `:location (12 3 main)`, which its parser reads back as the same s-expression, the Dafny
   and Boogie printers `{:location (12 3 main)}`; the C printer writes only invariants and variants, so the outputs
   in C and the roundtrip of the C examples do not change, and the examples that print C as Dafny have no loops.
   `TEQ.loop` and `Horn` get the attributes of the loop, so the location reaches the construction of the
   invariants.
   - `for`: a single `while`, whose head is before the test and after the step, the evaluation point of the
     witness; a `continue` is preceded by a copy of the step (`stepped`), instead of the former inner loop
     `while (true) { body; break }` with a flag for `break`, which `-vcgen` took for a loop without invariant and
     `-chc` gave predicates of its own.
   - `do-while` is `while (first || test)`, whose head also includes the entry: an invariant there holds at all
     evaluation points of the witness, sound, possibly weaker. Its location is that of `do`.
   - A `goto` copies the statement of its label, and `-teq` inlines calls: several loops share one location,
     whose invariants the writer joins by a disjunction.

Test: [examples/c/parsing/location.c](../examples/c/parsing/location.c) with `-print smt2`, whose output shows the
attribute of each kind of loop (`while`, `do`, `for` with `continue`, a tab before a loop, a loop in a function other
than `main`), and [for_break_continue.c](../examples/c/horn/for_break_continue.c) for the semantics of `continue`.

Later, outside the two packages: the printers of SMT-LIB, SV-LIB, Dafny and Boogie drop `:location`, as
`svlib.Printer.properties` drops `modifies`, since a validator of SV-LIB may reject the attribute. The scanner's
errors report 0-based positions (`yyline` as is). Further constructs extend the list of located keywords: `if` for
branching waypoints; the names `reach_error` and `__VERIFIER_error` are located values since Oct 15, 2026
(`Located("sym", text, line, column)`, which `Parser.Match` takes like a value), for the targets;
`__VERIFIER_assert` and `__VERIFIER_nondet_*` would follow the same scheme. Not yet located: the
assertions and nondeterministic calls (`Spec` has no attributes; a `Block` with attributes, as for `:tag` since
0.39, is flattened on the way), needed only for detailed violation witnesses; the target is not
threaded through the parser, since `reach_error()` is in the body of `__VERIFIER_assert`, which the grammar skips
(`Balanced` in `Grammar.body`): the writer scans the input again, which it reads anyway for the SHA-256.

Considered: the position on every token, in a second parameter list of `Keyword` and `Value`. It needs `()` at
every construction in all frontends (Scala 3.8.1 does not fill in an omitted list of defaults, `Keyword("(")` is a
function `Int => Keyword`, which a `val` without a type such as `sexpr.Syntax.lp` takes silently), a parser that
reads the position of the next token, and positions for the expansions of Typedefs, for constructs that need none
yet. It pays off only once statements in general have locations (location invariants at arbitrary statements).

`-chc` gives the witnesses of SV-LIB and Loops soon; the work specific to TEQ is the extraction of invariants
from proofs, which pays off on arrays only once the format has quantifiers.
