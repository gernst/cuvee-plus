# Architecture

Cuvée is a pipeline. A **source** turns the input file into a lazy stream of
core commands. **Stages** transform the commands. A **sink** prints them or
passes them to a solver. All stages share one representation, the core
([datastructures.md](datastructures.md)), so any frontend combines with any
transformation and any output.

```
 input.dfy ──► Source ──► Stage(Verify) ──► Stage(Simplify) ──► Sink(z3)
              (parse,      (transform)       (transform)         (print or
               resolve,                                           solve)
               check)                        Report ◄── results of each command
```

## Packages

| Package | Contents |
|---|---|
| `util` | `Name` (identifiers with an optional index), `Rational`, `Counter` (fresh indices), `Ref`, `Tool` (external processes), `Backtrack`. |
| `easyparse` | Parser combinators over token streams. `~` commits and `?~` backtracks. `Mixfix` handles prefix, postfix and infix operators with precedence and associativity. `P(...)` names parsers for error messages. |
| `easyprint` | Wadler-style pretty printing (`Doc`, `Group`, `Nest`, `line`). |
| `cuvee.sexpr` | The s-expression scanner and syntax for SMT-LIB. |
| `cuvee.core` | The common representation: `Type`, `Expr`, `Prog`, `Cmd`, `Fun`, `Attrs` and `State`, plus type checking (`Type.check`), substitution (`Subst`), overloading (`Overload`) and syntactic sugar (`Builtin`, `Sugar`). |
| `cuvee.smtlib` | SMT-LIB frontend (`Parser`, `Source`), `Printer`, and `Solver` (z3 and cvc5 as sinks). |
| `cuvee.boogie` | Boogie frontend and printer, with datatypes written like Dafny's (`data`). |
| `cuvee.c` | C frontend and printer, for integer programs with arrays as values. |
| `cuvee.yml` | SV-COMP task definitions (`Task`, read with SnakeYAML Engine), whose single C input file is read by the C frontend. |
| `cuvee.dafny` | Dafny frontend and printer, including the extensions for hybrid programs and parallel composition. |
| `cuvee.pipe` | `Source`, `Stage`, `Sink`, `Report`, `Pipe` and the `Printer` interface. |
| `cuvee.verify` | `Verify` (weakest preconditions to goals), `TEQ` (symbolic execution and trace equation systems), and `Horn` (constrained Horn clauses). |
| `cuvee.simplify` | `Simplify` (contextual simplification under a `Ctx`), `Arith` (polynomials over `Int` and `Real`), `Rewrite` (rewrite engine for conditional rules), and `FourierMotzkin` (linear constraints over the rationals). |
| `cuvee.transform` | `Flat` (records are replaced by their fields, equations of bound variables are inlined), `Split` (goals into individual obligations), and `Monomorph` (instances of polymorphic functions). |
| `cuvee` | `Cuvee` (main), `Config` (command line), `Error` and `Debug`. |

## A run

[`Cuvee.run`](../src/cuvee/Cuvee.scala) goes through these steps:

1. `Config.parse` reads the command line:
   - the input language from the file extension;
   - the transforms in order (`-verify`, `-teq`, `-chc`, `-flat`, `-split`, `-monomorph`, `-simplify`);
   - the printer (`-print`);
   - the sink (stdout, `-o`, `-z3`, `-cvc5`).
2. `config.input.source(reader)` parses the frontend's prelude first
   (`prelude.*`). It returns the initial `State`, which holds its
   declarations, and a lazy `LazyList[Cmd]`, which begins with these
   declarations and those that depend on the configuration (`hybrid.dfy`
   with `-hybrid`, see [hybrid.md](hybrid.md)), followed by the input, where
   commands that coincide with those of the prelude are dropped, e.g. when
   printed output is parsed again.
3. `config.stages(init, sink)` chains one `Stage` per transform in front of
   the sink. All stages start from the same initial state, and know the
   configuration. `config.input` and `config.output` are `Lang`s, each
   with the features (attributes) that it knows: its file extension, plus
   `teq` and `hybrid` added to both by `-teq` and `-hybrid`, also when the
   output is in another language (`Config.printing`). `Cuvee.pipe`
   wraps the printers in `Printer.filter`, which drops the top-level
   declarations with these features: the output printer of the sink by
   `config.output.features`, the printer of the reports, which is that of the
   input language, by `config.input.features`. The solver sink skips the
   declarations of `smt2` itself; further sinks, e.g. of tests, receive all
   commands. `Monomorph` keeps the polymorphic functions of
   `config.output.features`. `-print null` and `-print scala` replace only
   the printer of the output; transforms whose output a language cannot
   express (`hasMath`, e.g. `-chc` of C) print SMT-LIB instead.
4. `Pipe.run` feeds the commands, followed by the internal `Done`, through
   the chain. It reports each result (`Ack`, `Status`, `Model`, `Error`, ...)
   through `Report`. An `Error` stops the run unless the pipe is incremental;
   other exceptions are reported as `internal error` (stack trace with
   `-debug internal`) and always stop it. `Pipe.run` returns an exit code,
   1 for an error and 2 for an internal error, with which `Cuvee.main`
   exits.

### Stages and transforms

A [`Stage`](../src/cuvee/pipe/Stage.scala) buffers declarations (`Decl`) and
adds them to its state. A control command or query (`check-sat`, `push`,
`Done`, ...) flushes the buffer: it calls the stage's `Transform` with:

- the configuration of the run, e.g. its printer for debug output;
- the current state;
- the commands passed so far;
- the pending commands;
- the flushing command.

It then passes the result on to the next sink. `push` and `pop` save and
restore the prefix and the state. A transform is a plain function:

```scala
type Transform = (Config, State, List[Cmd], List[Cmd], Cmd) => List[Cmd]
```

The answers to several queries that a transform adds, e.g. `check-sat` and
`get-model` after `Horn`, are reported one by one (`Answers`).

- [`Verify`](../src/cuvee/verify/Verify.scala) replaces each procedure
  definition by a goal: `∀ in, out, globals. pre ⇒ wp(body, post)`.
  - Loops, iterations, calls (by contract), `old`, termination measures,
    differential equations and parallel composition ([hybrid.md](hybrid.md))
    each have a rule.
  - `old(e)` is eliminated first, by `Old.elim`, into fresh variables for the
    values at the entry.
- [`TEQ`](../src/cuvee/verify/TEQ.scala) replaces each procedure definition
  by a goal from symbolic execution with trace equation systems for loops,
  see [teq.md](teq.md).
- [`Horn`](../src/cuvee/verify/Horn.scala) translates procedures into Horn
  clauses over uninterpreted predicates: `p_pre`, `p_post`, and one predicate
  per program point after assignments, calls, loop heads, and joins, followed
  by `check-sat` and `get-model`, whose model is printed in the language of the
  input.
  - Procedures with a body have predicates and no contract, which is an
    error, except for `requires` of `main` (in C, the globals are zero; their
    initializers are assignments at the beginning of `main`). Those that no procedure calls are entry points, `requires ⇒ p_pre`.
  - Procedures without body have no predicates; calls instantiate their
    contract (`Verify.instance`, also the type parameters), whose
    precondition's conjuncts are goals and whose postcondition's conjuncts
    are facts. Polymorphic procedures that are only specified thus yield
    monomorphic clauses.
  - The body starts from `p_pre`; branches extend the facts of the first
    clause by the test, and `break`, `continue`, `return`, and the end of a
    block lead directly to the predicate of their target, whose variables are
    those in scope there.
  - Annotations (`invariant`, `decreases`), preconditions of procedures
    without body, and assertions are goals in the head of clauses,
    `facts ⇒ φ`.
  - The `-chc` tests use [examples/dafny/horn](../examples/dafny/horn) and
    [examples/boogie/horn](../examples/boogie/horn), whose procedures with a
    body have no contracts.
- [`Simplify`](../src/cuvee/simplify/Simplify.scala) rewrites assertions and
  function definitions to a fixpoint, and simplifies procedures statement by
  statement. Assertions are normalized into clauses (`Normalize`) before
  simplification and after each round of it, which repeats while they change
  (`Simplify.apply`), such that e.g. the equations of `let` are simplified in
  the context; they are dropped if they simplify to `true`.
  `Normalize.lift` lifts `ite` out of the terms of atoms to the level of
  formulas, `A[ite(c, a, b)]` to `ite(c, A[a], A[b])`, but not out of
  binders, derivatives, and `old` inside of `A`; `Split` uses it.
  - All methods take `(config, state, ctx, ...)`. The context `Ctx` holds the
    facts known at the current position and the rewrite rules, which are
    extracted from the assertions, lemmas, and function definitions with the
    attribute `:rw` (`Rules.from`) and are kept as they are; a definition
    whose body is a match on a parameter gives one rule per case, with the
    pattern in place of the parameter (overlapping patterns are not handled).
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
    seen from the current position (`Ctx.existential`): bound by `exists`
    (`Ctx.exists`), or by `forall` (`Ctx.forall`) below an odd number of
    negations and premises (`Ctx.flip` swaps `universal` and `existential`),
    and `x` occurs nowhere else: not in `e`, not in the facts of the context (`Ctx.used`,
    which includes the primed variables of derivatives), and `e` has no
    variables bound inside the scope of `x`. `bind` then drops `x`. This
    relies on the context recording all siblings between the binder and the
    equation, which holds for `and`, `or`, `not`, `==>`, and binders only;
    the branches of `ite`, the bodies of `let`, `match`, and `invs`, and
    neutral positions forget which variables are universal and existential
    (`Ctx.neutral`); the variables of `let`, `match`, and the combinators are
    neither (`Ctx.bind`).
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
  - Derivatives are computed by the rules of dL ([hybrid.md](hybrid.md)).
- [`Rewrite`](../src/cuvee/simplify/Rewrite.scala) applies conditional rules
  innermost first, also as a library. Its methods take
  `(config, state, ctx, ...)` as well; matches are substitutions, and side
  conditions are decided by `Simplify.simplify` in the context. Matching
  below the combinators of TEQs is described in [teq.md](teq.md).
- [`Flat`](../src/cuvee/transform/Flat.scala) eliminates records
  (non-recursive datatypes with one constructor), whose declarations are
  dropped: functions take their fields, functions with records as results are
  split into one per field (`f_sel`), also definitions, bound variables become
  their fields, equations conjunctions, and selectors and testers are reduced;
  terms of records are constructors, selectors, `ite`, and applications of
  such functions (not `let`, `match`, `as`), and records that instantiate type
  parameters (e.g. in arrays) are errors. It also inlines the equations
  `x == t` of the antecedents of clauses `∀ xs. φ₁ ∧ ... ∧ φₙ ⇒ ψ` whose
  variable is among `xs` and not in `t` (`Flat.eliminate`).
- [`Split`](../src/cuvee/transform/Split.scala) splits goals and lemmas into
  individual obligations, after lifting `ite` out of the terms of atoms
  (`Normalize.lift`), such that it is split by its test as well.
- [`Monomorph`](../src/cuvee/transform/Monomorph.scala) replaces polymorphic
  functions by their instances, which are emitted before their first use.

### Sinks

A [`Sink`](../src/cuvee/pipe/Sink.scala) answers each command with a result
and the next sink.

- `Print` writes the commands with the configured printer.
- `Collect` buffers them (used in tests).
- `Tee` duplicates the stream.
- [`Solver.sink`](../src/cuvee/smtlib/Solver.scala) runs z3 or cvc5 as a
  process:
  - Goals and lemmas are checked for validity in a `push`/`pop` scope; lemmas
    are then asserted. Lemmas with the attribute `:free` are assumed without
    proof, like axioms.
  - Procedures and global variables must have been eliminated by `-verify` or
    `-chc`.

## Frontends

Each frontend follows the same structure (see `cuvee.dafny` and
`cuvee.boogie`):

1. **Scanner** (`Scanner.flex`): jflex produces `Scanner.java`. Regenerate it
   from the repository root with
   `jflex -q --nobak src/cuvee/<lang>/Scanner.flex`. Keywords and symbols
   become `Token`s.
2. **Syntax** (`Syntax.scala`): an untyped AST close to the concrete syntax,
   with names as strings.
3. **Grammar** (`Grammar.scala`): easyparse parsers from tokens to the AST.
   They build syntax only: no lookups in `state` or scopes, all resolution
   happens in the parser.
   - Operators and their precedences are tables for `Mixfix`.
   - `translate` maps the frontend's names onto core names, e.g.
     `int → Int`, `&& → and`, `seq → Seq`.
4. **Parser** (`Parser.scala`): resolves the AST into core against a mutable
   `state` and a `Scope` of type parameters and variables.
   - Declarations update `state` immediately, so later commands see them.
   - Each expression and program body is type checked by `state.exprs.check`
     or `state.progs.check`. These call `Type.check` and then
     `Overload.apply`, which replaces the generic arithmetic operators of the
     prelude by their `Int`, `Real` or `Seq` implementations.
   - Axioms, lemmas, and goals are single formulas with optional type
     parameters and attributes, `lemma <a> {:rw} φ` (Boogie:
     `lemma <a> {:rw} φ;`). The formula is resolved and checked in the scope
     of the type parameters (`assertion`). In Dafny, `if φ then ψ` without
     `else` is `φ ==> ψ` anywhere (the parser translates `Ite` whose else
     branch is `true`); the guarded cases of the updates of combinators begin
     with `case`, `case φ => e`, so an if-then-else there needs no parentheses.
   - Dafny's chained comparisons `0 <= i < n` and `x == y == z` are
     conjunctions: the comparison operators associate to the left in the
     grammar, and the parser expands a comparison whose left operand is
     another (unparenthesized) comparison (`Parser.chain`). Parenthesized expressions are `Tuple(List(e))` in the syntax,
     which is how `(x == y) == b` stays apart. Chains must not mix `<`/`<=`
     with `>`/`>=`.
5. **Prelude** (`resources/cuvee/<lang>/prelude.*`), in the frontend's own
   syntax: the built-in sorts, the generic operators, and definitions such as
   Dafny's tuples. Each declaration names the languages that it is part of by
   attributes named after their file extensions, `{:dfy} {:bpl} {:smt2} {:c}`
   (in SMT-LIB `:smt2 ...`, inside `par`). The output in such a language
   drops it, e.g. the tuples are `{:dfy}` only, so SMT-LIB output declares
   them as datatypes, and Dafny's `map` reaches the solvers as a declared
   sort. Declarations that coincide with existing ones leave the state
   unchanged (`State.unless`). Transforms see the prelude's declarations,
   e.g. `Monomorph` ignores those that are part of the output language.
   `Trace` is in no prelude: it exists only with `-teq` ([teq.md](teq.md)).
6. **Printer** (`Printer.scala`): core back to concrete syntax with
   easyprint.
   - It reverses `translate` and recognises sugar, e.g. sequence literals,
     `x in s`, `s[i..j]`, and `a != b`.
   - The Dafny printer prints conjunctions of comparisons that are linked by
     their operands as chains, and treats the comparison operators as
     non-associative, so a comparison as operand of a comparison is
     parenthesized and is not read back as a chain.
   - Constructs that the language lacks raise an error.

The syntax of the combinators of trace equation systems is in
[teq.md](teq.md), that of hybrid programs in [hybrid.md](hybrid.md).

The SMT-LIB frontend is an exception: it reads s-expressions with the shared
`sexpr` scanner and turns them into core directly. The C frontend is another:
it starts from its own prelude (`resources/cuvee/c/prelude.bpl`, in Boogie),
which declares the core theory with arithmetic on `Int` only, arrays, and the
background theory of C, builds expressions on `Int` and `Bool` directly, and parses the whole translation unit at once, so
that it can infer the global variables that each function and each loop
modifies. SV-COMP task definitions (`.yml`) defer to the C frontend: their
`Source` overrides `input`, which reads the input on demand, to load the task
and parse its input file, relative to the task; the output is printed as C
(`Lang.output`).

## Errors and debugging

`cuvee.Error(msg, info*)` is a result as well as an exception.
`Error.report(msg, info*) { require(...) }` wraps a check and raises the
error with its context. Errors are reported as results and do not crash the
run, with the exceptions listed in [TODO.md](../TODO.md).
Debug output is enabled per module by `-debug <modules>`: `solver` traces
the communication with the solvers, `simplify` and `rewrite` print the steps
that change an expression with the printer of the configuration.

## Tests

The tests use utest and run with `mill -i test` (four forked groups, each
reporting `Tests: n, Passed: n, Failed: n`; failures are marked `X`).
A single run is `mill -i run <options> <file>`, e.g.
`mill -i run -teq -simplify examples/dafny/vcgen/sum.dfy`. Their sources are in
`test/src/cuvee/test/`, by frontend:

- Unit tests build core terms directly, or check short inputs with
  `Examples.check(ext, text, options*)`, which returns the errors reported for
  them.
- Hybrid programs and other inputs with polymorphic axioms are not passed to
  solvers; their tests generate the goals only (`-print null`).
- Example tests run `cuvee.Cuvee.run` on the files in `examples/`, which has
  a subfolder per language (`dafny`, `boogie`, `c`, `smtlib`, `yml`) and per
  transformation (`dafny/vcgen`, `dafny/horn`, `hybrid`, `simplify`,
  `transform`), through `Examples.find` and `Examples.tests`; the Dafny
  examples are all in subfolders, the language features in `dafny/language`,
  and the loops for trace equation systems in `dafny/teq` (parsed only, not
  verified yet):
  - every file must parse;
  - the Dafny printer must roundtrip;
  - `examples/simplify/*.smt2` must produce `*.expected.smt2`;
  - `examples/dafny/vcgen/*.dfy` must verify (or fail, as declared in their first
    line) with `-verify -z3` and `-chc -z3`;
  - the Boogie and C examples likewise, and the programs of the Dafny and
    Boogie examples must roundtrip through SMT-LIB.
- The tests of trace equation systems are listed in [teq.md](teq.md).
