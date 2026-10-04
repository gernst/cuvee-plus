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
| `cuvee.boogie` | Boogie frontend and printer. |
| `cuvee.c` | C frontend and printer, for integer programs with arrays as values. |
| `cuvee.dafny` | Dafny frontend and printer, including the extensions for hybrid programs and parallel composition. |
| `cuvee.pipe` | `Source`, `Stage`, `Sink`, `Report`, `Pipe` and the `Printer` interface. |
| `cuvee.verify` | `Verify` (weakest preconditions to goals), `TEQ` (symbolic execution and trace equation systems), and `Horn` (constrained Horn clauses). |
| `cuvee.simplify` | `Simplify` (contextual simplification under a `Ctx`), `Arith` (polynomials over `Int` and `Real`), `Rewrite` (rewrite engine for conditional rules), and `FourierMotzkin` (linear constraints over the rationals). |
| `cuvee.transform` | `Flat` (record arguments of predicates become their fields), `Split` (goals into individual obligations), and `Monomorph` (instances of polymorphic functions). |
| `cuvee` | `Cuvee` (main), `Config` (command line), `Error` and `Debug`. |

## A run

[`Cuvee.run`](../src/cuvee/Cuvee.scala) goes through these steps:

1. `Config.parse` reads the command line:
   - the input language from the file extension;
   - the transforms in order (`-verify`, `-teq`, `-chc`, `-flat`, `-split`, `-monomorph`, `-simplify`);
   - the printer (`-print`);
   - the sink (stdout, `-o`, `-z3`, `-cvc5`).
2. `config.source(reader)` parses the frontend's prelude first. It returns
   the initial `State`, which holds the prelude's declarations, and a lazy
   `LazyList[Cmd]` of the input.
3. `config.stages(init, sink)` chains one `Stage` per transform in front of
   the sink. All stages start from the same initial state, and know the
   configuration.
4. `Pipe.run` feeds the commands, followed by the internal `Done`, through
   the chain. It reports each result (`Ack`, `Status`, `Model`, `Error`, ...)
   through `Report`. An `Error` stops the run unless the pipe is incremental.

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
    differential equations (differential cuts, then weakening) and parallel
    composition (assumption-commitment) each have a rule.
  - `old(e)` is eliminated first, by `Old.elim`, into fresh variables for the
    values at the entry.
- [`TEQ`](../src/cuvee/verify/TEQ.scala) replaces each procedure definition
  by a goal from symbolic execution, after section 4 of the paper.
  - A `Path` holds the fresh variables for nondeterministic choices, the
    values of the variables as a substitution, and the assumptions, branch
    conditions, and checks along the way. Choices `if *` become branches on
    fresh booleans, calls go by contract.
  - Each loop yields a single path (theorem 4.8), which assumes its trace
    equation system (definition 4.4): one `Trace` per modified variable,
    whose update has a case per path through the body, the counter
    `K = counter(0, 1, n)`, and the iteration constraint `Invs`, and which
    checks that the body executes safely from the current state.
  - The goal is that all checks hold and the postcondition follows on every
    path.
- [`Horn`](../src/cuvee/verify/Horn.scala) translates procedures into Horn
  clauses over uninterpreted predicates: `p_pre`, `p_post`, and one predicate
  per program point, followed by `check-sat` and `get-model`, whose model is
  printed in the language of the input.
- [`Simplify`](../src/cuvee/simplify/Simplify.scala) rewrites assertions and
  function definitions to a fixpoint, and simplifies procedures statement by
  statement.
  - All methods take `(config, state, ctx, ...)`. The context `Ctx` holds the
    facts known at the current position and the rewrite rules.
  - Each round (`once`) simplifies the subterms first and dispatches on the
    built-in functions; afterwards, one rewrite step with the rules of the
    context is tried at the top (`Rewrite.step`), until a fixpoint.
  - Arithmetic is normalised into polynomials (`Arith`); comparisons become
    `0 < p` and `0 <= p` with positive coefficients on both sides.
  - Derivatives are computed by the rules of dL.
- [`Rewrite`](../src/cuvee/simplify/Rewrite.scala) applies conditional rules
  innermost first, also as a library. Its methods take
  `(config, state, ctx, ...)` as well; matches are substitutions, and side
  conditions are decided by `Simplify.simplify` in the context.
- [`Flat`](../src/cuvee/transform/Flat.scala) flattens record arguments of
  Horn predicates.
- [`Split`](../src/cuvee/transform/Split.scala) splits goals and lemmas into
  individual obligations.
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
  - It first declares the sorts and datatypes of the frontend's prelude that
    SMT-LIB lacks (`Solver.prelude`), e.g. Dafny's tuples and events.
  - Goals and lemmas are checked for validity in a `push`/`pop` scope; lemmas
    are then asserted.
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
5. **Prelude** (`resources/cuvee/<lang>/prelude.*`), in the frontend's own
   syntax. It declares the built-in sorts and the generic operators, and for
   Dafny also tuples, `chan` and `event`.
6. **Printer** (`Printer.scala`): core back to concrete syntax with
   easyprint.
   - It reverses `translate` and recognises sugar, e.g. sequence literals,
     `x in s`, `s[i..j]`, and `a != b`.
   - Constructs that the language lacks raise an error.

The combinators of trace equation systems are written in each language as
follows, where updates with several cases are guarded:

| Combinator | Dafny and Boogie | SMT-LIB |
|---|---|---|
| `Trace` | `trace(e, for Y, Z do x, y, z => u)` | `(trace (x e) ((y Y) (z Z)) u)` |
| `Maps` | `map(for Y yield y => u)` | `(map ((y Y)) u)` |
| `Invs` | `all(for Y check y => φ)` | `(all ((y Y)) φ)` |
| update | `if φ₁ then e₁, if φ₂ then e₂` | `(cases (φ₁ e₁) (φ₂ e₂))` |

The SMT-LIB frontend is an exception: it reads s-expressions with the shared
`sexpr` scanner and turns them into core directly. The C frontend is another:
it starts from the SMT-LIB prelude, builds expressions on `Int` and `Bool`
with the sugar directly, and parses the whole translation unit at once, so
that it can infer the global variables that each function modifies.

## Errors and debugging

`cuvee.Error(msg, info*)` is a result as well as an exception.
`Error.report(msg, info*) { require(...) }` wraps a check and raises the
error with its context. Errors are reported as results and do not crash the
run, with the exceptions listed in [TODO.md](../TODO.md).
Debug output is enabled per module by `-debug <modules>`: `solver` traces
the communication with the solvers, `simplify` and `rewrite` print the steps
that change an expression with the printer of the configuration.

## Tests

The tests use utest and run with `mill -i test`. Their sources are in
`test/src/cuvee/test/`, by frontend:

- Unit tests build core terms directly.
- Example tests run `cuvee.Cuvee.run` on the files in `examples/`, which has
  a subfolder per language (`dafny`, `boogie`, `c`, `smtlib`) and per
  transformation (`dafny/vcgen`, `simplify`, `transform`), through
  `Examples.find` and `Examples.tests`:
  - every file must parse;
  - the Dafny printer must roundtrip;
  - `examples/simplify/*.smt2` must produce `*.expected.smt2`;
  - `examples/dafny/vcgen/*.dfy` must verify (or fail, as declared in their first
    line) with `-verify -z3` and `-chc -z3`, those without loops also with
    `-teq -z3`;
  - the Boogie and C examples likewise, and the programs of the Dafny and
    Boogie examples must roundtrip through SMT-LIB.
- The rewrite engine is tested with the examples of the paper (counters,
  summations, `selects`), also on the goals of `-teq`.
