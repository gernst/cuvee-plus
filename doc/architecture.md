# Architecture

Cuvée is a pipeline. A **source** turns the input file into a lazy stream of
core commands. **Stages** transform the commands. A **sink** prints them or
passes them to a solver. All stages share one representation, the core
([datastructures.md](datastructures.md)), so any frontend combines with any
transformation and any output.

```
 input.dfy ──► Source ──► Stage(VCGen) ──► Stage(Simplify) ──► Sink(z3)
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
| `cuvee.svlib` | SV-LIB frontend (`Parser`, which extends the SMT-LIB parser by the statements and properties of SV-LIB, `Source`) and `Printer`. |
| `cuvee.yml` | SV-COMP task definitions (`Task`, read with SnakeYAML Engine), whose single input file is read by the frontend of its extension, C or SV-LIB; a missing input file is reported as the task writes it, independent of the directory; the witnesses of SV-COMP for C (`Witness`, written with SnakeYAML Engine). |
| `cuvee.dafny` | Dafny frontend and printer, including the extensions for hybrid programs and parallel composition. |
| `cuvee.lean` | Printer of the logic in Lean 4 (`-print lean`), output only. |
| `cuvee.pipe` | `Source`, `Stage`, `Sink`, `Report`, `Pipe` and the `Printer` interface. |
| `cuvee.verify` | `VCGen` (weakest preconditions to goals), `TEQ` (symbolic execution and trace equation systems), and `Horn` (constrained Horn clauses). |
| `cuvee.simplify` | `Simplify` (contextual simplification under a `Context`), `Arith` (polynomials over `Int` and `Real`), `Rewrite` (rewrite engine for conditional rules), `FourierMotzkin` (linear constraints over the rationals), and `Fuse` (fixpoint fusion of recursive functions, `-fuse`). |
| `cuvee.prove` | the deduction engine of `-prove` ([prove.md](prove.md)): `Prove` (the transform), `Simplify` and `Rewrite` (the traversal and the matcher, copied from `cuvee.simplify` and adapted, independent of it), `Context` with `Classes` (congruence closure), `Linear` and `Simplex` (linear arithmetic over the rationals), `Views` (the per-variable projections of traces of several accumulators), and its own `Arith`, `Normalize`, `Rule`. |
| `cuvee.transform` | `Flat` (records are replaced by their fields, equations of bound variables are inlined), `Split` (goals into individual obligations), `Monomorph` (instances of polymorphic functions), and `Fallback` (trace equation systems in first-order logic). |
| `cuvee` | `Cuvee` (main), `Config` (command line), `Error` and `Debug`. |

## A run

[`Cuvee.run`](../src/cuvee/Cuvee.scala) goes through these steps:

1. `Config.parse` reads the command line:
   - the input language from the file extension;
   - the transforms in order (`-vcgen`, `-teq`, `-chc`, `-flat`, `-split`, `-monomorph`, `-fallback`, `-fuse`, `-simplify`, `-prove`),
     and `-rules`, which makes `-simplify` report the rules it applies (see [simplifier.md](simplifier.md));
   - the printer (`-print`);
   - the sink (stdout, `-o`), the solver (`-z3`, `-cvc5`), which checks the
     output, and the answers of `-verify`, with or without solver;
     `Config.receiver` builds the sink from the final configuration.
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
   output is in another language (`Config.printing`). Each sink
   states the features that its receiver knows (`Sink.knows`): a printing
   sink those of `config.output.features`, the solver sink `smt2`.
   `Cuvee.pipe` puts `Sink.filter` in front of the sink, which drops the
   top-level declarations with these features and acknowledges them
   (`Sink.known`); further sinks, e.g. of tests, are behind the filter and
   see what the receiver sees. The solver sink passes all other declarations
   without attributes, e.g. those of `{:ho}`, which a solver may reject, and
   the assertions with their attributes `:named` and `:pattern` only. `Monomorph` keeps the polymorphic functions of
   `config.output.features`. `-known <features>` adds features to those of
   the output, e.g. `-print c -known dfy,teq,rw` prints the program of a
   Dafny file without its logic: `teq` keeps the declarations and lemmas of
   the lemma database out of the output (they are declared in the input, as
   with `-teq`, but without its transform).
   `-print null` and `-print scala` replace only
   the printer of the output; transforms whose output a language cannot
   express (`hasMath`, e.g. `-chc` of C) print SMT-LIB instead. Lean
   (`Lang.lean`) is an output only, which knows the built-in declarations of
   all languages: its printer maps them to Lean (booleans to propositions,
   arrays to functions, sequences to lists, tuples to products, Mathlib's
   `ℝ` and `Set`) or rejects them, like multisets, finite maps, bitvectors,
   and programs; the combinators of `-teq` are the functions of
   [lean/TEQ/Semantics.lean](../lean/TEQ/Semantics.lean).
   Datatypes are inductive types whose selectors are not declared, free
   lemmas and axioms are axioms,
   the other lemmas theorems and goals examples, proved `by sorry`, rewrite
   rules `@[simp]`; the output assumes `open Classical`.
4. `Pipe.run` feeds the commands, followed by the internal `Done`, through
   the chain. It reports each result (`Ack`, `Status`, `Model`, `Error`, ...)
   through `Report`. An `Error` stops the run unless the pipe is incremental;
   other exceptions are reported as `internal error` (stack trace with
   `-debug internal`) and always stop it. `Pipe.run` returns an exit code,
   1 for an error and 2 for an internal error, with which `Cuvee.main`
   exits. `Cuvee.main` runs the pipe on a thread with a stack of 1 GB, for
   deeply nested input, e.g. the outputs of the reducers of SV-COMP.

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

- [`VCGen`](../src/cuvee/verify/VCGen.scala) replaces each procedure
  definition by a goal: `∀ in, out, globals. pre ⇒ wp(body, post)`.
  - Loops, iterations, calls (by contract), `old`, termination measures,
    differential equations and parallel composition ([hybrid.md](hybrid.md))
    each have a rule.
  - `old(e)` is eliminated first, by `Old.elim`, into fresh variables for the
    values at the entry.
  - An assertion (`Spec(xs, pre, post)` with `pre` not `true`) is assumed
    once it is checked, `pre ∧ (pre ⇒ ∀ xs. post ⇒ wp)`, as in Boogie and
    Frama-C/WP: equivalent to `pre ∧ wp`, but the goals after it have `pre`
    as hypothesis, also the separate ones of `-split`.
- [`TEQ`](../src/cuvee/verify/TEQ.scala) replaces each procedure definition
  by a goal from symbolic execution with trace equation systems for loops,
  one trace per strongly connected component of the read relation of a loop's
  variables, of several accumulators for a cycle (`TEQ.system`);
  with an entry point (`Config.entryPoint`) only that of the entry point,
  whose calls are inlined, see [teq.md](teq.md).
- [`Horn`](../src/cuvee/verify/Horn.scala) translates procedures into Horn
  clauses over uninterpreted predicates: `p_pre`, `p_post`, and one predicate
  per program point after assignments, calls, loop heads, and joins, followed
  by `check-sat` and `get-model`, whose model is printed in the language of the
  input.
  - Procedures with a body have predicates and no contract, which is an
    error, except for `requires` of `main` (in C, the globals are zero; their
    initializers are assignments at the beginning of `main`). The entry
    point (`Config.entryPoint`: `-entry`, or `main` in C) has the clause
    `requires ⇒ p_pre`; the other procedures have trivial contracts, their
    preconditions are inferred from their calls. Outside C and SV-LIB (whose
    entries are its `verify-call` commands), `-chc` needs `-entry`; a C
    program without `main` and without `-entry` is an error.
  - Procedures without body have no predicates; calls instantiate their
    contract (`VCGen.instance`, also the type parameters), whose
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
  function definitions to a fixpoint under the facts of the context, with
  conditional rewrite rules ([`Rewrite`](../src/cuvee/simplify/Rewrite.scala)),
  see [simplifier.md](simplifier.md).
- [`Prove`](../src/cuvee/prove/Prove.scala) is the second engine for the goals of trace equation systems
  (`-prove`), with congruence closure and a simplex as its context, the views of traces of several accumulators, rules over whole
  cycles and forward lemmas ([`Forward`](../src/cuvee/prove/Forward.scala)), see [prove.md](prove.md).
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
- [`Split`](../src/cuvee/transform/Split.scala) splits goals, lemmas, and
  axioms into individual obligations, after lifting `ite` out of the terms of
  atoms (`Normalize.lift`), such that it is split by its test as well; the
  parts of a named assertion are named apart, `n_1`, `n_2`, ..., since
  solvers reject a name that is already defined.
- [`Monomorph`](../src/cuvee/transform/Monomorph.scala) replaces polymorphic
  functions by their instances, which are emitted before their first use.
- [`Fallback`](../src/cuvee/transform/Fallback.scala) lowers trace equation
  systems into first-order logic for solvers (`-fallback`, see
  [teq.md](teq.md)).

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
  - Procedures and global variables must have been eliminated by `-vcgen` or
    `-chc`.
- [`Verify`](../src/cuvee/pipe/Verify.scala) (`-verify`) answers
  `correct`, `incorrect`, or `unknown` (the cases `Correct`, `Incorrect`, `Unknown` of
  [`Status`](../src/cuvee/core/Cmd.scala))
  to `verify-call`, and to `Done` if there was no `verify-call`, aggregated over
  the obligations so far; the answers are reported on stdout, the output is not
  printed. The commands go to the solver directly, as with the solver sink but
  without its parser state, since models and other answers are not reported.
  - Each obligation has the status that it has if the program is correct
    (`Verify.expected`): goals and lemmas `unsat` of their negation, `check-sat`
    `sat`, since a model of the clauses of `Horn` gives the invariants; a
    `check-sat` of the input counts as well. The answer of the solver holds if
    it is the expected one, refutes if it is the opposite one, unless the goal
    is `:abstract` (a loop without invariant in `VCGen`, a goal lowered by
    `Fallback`) or applies a function declared `:abstract` (`Cmd.funs`), or
    one defined in terms of such, e.g. the bit operations of the C prelude,
    and is undecided otherwise. Without solver, only the goal
    `false` is refuted.
  - The outcome is incorrect once an obligation is refuted, otherwise unknown
    once one is undecided; all obligations are checked.
  - Refuted goals are no errors, such that all commands are processed;
    procedures, global variables, and tags are an error, since they would be
    answered correct without checking anything (they need `-vcgen`, `-teq`, or
    `-chc`).
- [`Witnessing`](../src/cuvee/yml/Witness.scala) (`-witness <file>`, which implies `-verify`) wraps the sink of
  `-verify` and writes the witness of SV-COMP for its answer to the end of the input of a C program: a correctness
  witness for `correct`, a violation witness for `incorrect`, both without content for now (format 2.0, the strings
  quoted, since readers of YAML 1.1 take the creation time for a date otherwise), with the input file as given on
  the command line or relative to the task definition, its SHA-256, and the data model of `-arch` or of the task.

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
   - Axioms and goals are single formulas with optional type parameters and
     attributes, `axiom <a> {:rw} φ`, as are lemmas in Boogie,
     `lemma <a> {:rw} φ;`. Lemmas in Dafny are written as in Dafny,
     `lemma {:rw} name<a>(xs) returns (ys) requires φ ensures ψ`, and are the
     formula `forall xs :: φ ==> exists ys :: ψ` (the conjunctions of the
     clauses, without the quantifiers if there are no variables and without
     the implication if there are no `requires`), named by the attribute
     `:named`; a lemma without a body is free (`:free`), one with the empty
     body `{}` is to be proved, other bodies are not supported yet. The
     formula is resolved and checked in the scope of the type parameters
     (`assertion`). In Dafny, `if φ then ψ` without
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
background theory of C: the bit operations `&`, `|`, `^`, `~` and shifts by
non-constants are uninterpreted functions declared `:abstract`, with rules of
the simplifier for the operands 0 and 1 (`{:smt2} {:rw}`, not passed to the
solvers), such that `-verify` takes a refutation that depends on them for no
counterexample (`pipe.Verify`). It builds expressions on `Int` and `Bool` directly, and parses the whole translation unit at once, so
that it can infer the global variables that each function and each loop
modifies. Functions and loops with ACSL `assigns` or `loop assigns` clauses
modify the global variables listed there instead (their identifiers, e.g. `a`
for `a[0..N-1]`), which `Type.check` holds against the body, unless `-teq` or
`-chc` is among the transforms, which infer them always (`c.Parser.assigned`,
the parameter `infer` set by `c.Source`). The keywords `while`, `do` and `for` are located tokens
(`easyparse.Token.Located`, with line and column from 1, a tab one column), which match as keywords and which the
grammar reads by `L(name)`; each loop of the core gets the attribute `:location (line column function)` of its
keyword, an s-expression that all printers but C's print, for the locations of witnesses
([ideas/witnesses.md](../ideas/witnesses.md)). A `for` is a single loop, located at the `for`, whose `continue`s
are preceded by a copy of the step (`c.Parser.stepped`), those of nested loops not; a `do-while` is located at the
`do` ([location.c](../examples/c/parsing/location.c),
[for_break_continue.c](../examples/c/horn/for_break_continue.c)). SV-COMP task definitions (`.yml`) defer to the frontend of their
input file, C or SV-LIB: their `Source` overrides `input`, which reads the
input on demand, to load the task and parse its input file, relative to the
task; the output is printed in the language of the input file (`Config.parse`).

The SV-LIB frontend (`.svlib`, [SV-LIB 1.0](https://arxiv.org/abs/2511.21509))
extends the SMT-LIB parser: `define-proc` with local variables, the
statements `sequence`, `choice`, `if` without else, `(! s attrs)`, and the
commands `annotate-tag` and `verify-call`, which are core commands
`AnnotateTag` and `VerifyCall`, since an annotation may follow the procedure
it belongs to, up to the `verify-call` that it applies to. Properties
(`:requires`, `:ensures`, `:invariant`, `:decreases`, `:check-true`) are
attributes of loops and of procedure bodies, written inline or linked by
`annotate-tag` to the statements with the `:tag`; the parser resolves their
variables in the scope of the tagged statement and their functions in the
state at the command, and keeps a table from tags to these scopes. The
stages collect the `AnnotateTag` commands in `State.annotations`, and
`VCGen` and `Horn` attach them to the loops of a body
(`State.annotated`) when they verify it at the `VerifyCall`, which flushes
the stages like `check-sat`. `VCGen` adds the goal that the arguments
satisfy the precondition, `Horn` the entry clause `p_pre(args, gs)`, in
which the constants of the script are quantified together with the axioms
about them, since Horn solvers reject free constants, and a `check-sat`.
`(at x tag)` is `old(x)` when `tag` is that of the procedure body and `x` a
global variable or an input; `:check-true` of a loop is checked at every
evaluation of its test without being assumed, elsewhere it is asserted before
the statement. Tags on other statements are rejected, since the core has no
annotations there, and so are `define-procs-rec`, labels and gotos, the
properties `:recurring` and `:not-recurring`, `:decreases-lex`, witnesses and traces. The modified
global variables of procedures and loops are inferred, as in C. The verdict
of a task is decided by the BenchExec module [cuvee.py](../cuvee.py) from the
answers of `-verify` to the `verify-call`s.

### Programs in SV-LIB and in the SMT-LIB of Cuvée

Both languages share the logic (terms, sorts, datatypes, functions, and the
combinators of trace equation systems, printed by `smtlib.Printer`) and
`declare-var` for global variables, but write programs differently. The
SMT-LIB dialect (`smtlib.Parser.prog`) is the core's own notation, printed one
to one; SV-LIB (`svlib.Parser.stmt`) is the language of the tasks, read into
the same core:

| | SMT-LIB of Cuvée | SV-LIB |
|---|---|---|
| procedure | `(define-proc p (in) (out) body attrs)`, the local variables in the block of the body | `(define-proc p (in) (out) (locals) body)` |
| contract | attributes after the body, `:requires`, `:ensures`, `:modifies` | annotations of the body, `(! body :requires φ :ensures ψ)` |
| modified globals | `:modifies (x ...)`, required: the other globals must not be assigned (`Type.check`) | inferred from the assignments and calls (`svlib.Parser.modifies`); a `:modifies` of the core is dropped by `svlib.Printer` |
| loop properties | attributes after the body, `(while test body :invariant φ)` | `(! (while test body) :invariant φ)`, or `annotate-tag` on a `:tag` |
| blocks | `(block (locals x ...) s ...)`, with local variables anywhere | `(sequence s ...)`, without local variables |
| assertions | `(assert φ)`, `(abort)`, `(spec (xs) pre post)` | `(! (sequence) :check-true φ)`, a location invariant |
| choices | `(choose s ...)`, `(if test s₁ s₂)` with both branches | `(choice s ...)`, `(if test s)` without else |
| values at the entry | `(old x)` | `(at x tag)` with the tag of the body |
| polymorphism, declarations | `(define-proc p (par (a) ...) ...)`, `declare-proc` | not supported (`svlib.Printer`) |
| further statements | `iter`, `ode`, `par` (hybrid programs) | `label`, `goto`, `define-procs-rec`, rejected by the parser |
| what is verified | every procedure against its contract (`-vcgen`), or the entry point (`-entry`, `-teq`, `-chc`); `annotate-tag` and `verify-call` are read as well, e.g. in printed SV-LIB that is parsed back | the `verify-call` commands, one answer each with `-verify` |

A script printed as SV-LIB (`-print svlib`) and read back keeps its meaning but
not its text: the contracts become annotations, the modifies clauses are
inferred again, and blocks with local variables outside the body are not
printable.

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
A single run is `./Cuvee.sh <options> <file>` (after the assembly, see the
README; options in [options.md](options.md)), e.g.
`./Cuvee.sh -teq -prove examples/dafny/vcgen/sum.dfy`. Their sources are in
`test/src/cuvee/test/`, by frontend:

- Example tests: every file in `examples/` (except `datastructures`) states its
  command line in its first line, as a comment that can be pasted into a shell
  in the root of the repository, e.g.
  `; ./Cuvee.sh -simplify examples/smtlib/simplify/arith.smt2`. Its expected output is
  `name.out` (stdout) and `name.err` (stderr, the reports), where a missing
  file stands for no lines. `./Cuvee.sh -test <file>` checks an example
  ([test/Expected.scala](../src/cuvee/test/Expected.scala)), and so does
  `Examples.checked` in the test suites, which prints `./Cuvee.sh -test
  <file>` for each example. The reports are compared as text, and so is the
  output of examples in a directory named `printing`; other outputs are
  compared as commands, parsed in the language of the output. The output is
  captured in memory (`Config.stdout`, `Config.stderr`), tests never write
  files; an expected output is regenerated by hand with
  `./Cuvee.sh <options> <file> > name.out 2> name.err` and reviewed.
  `examples` has two levels, `examples/<language>/<module>/<file>`, no deeper:
  a folder per language of the input (`dafny`, `boogie`, `c`, `smtlib`,
  `svlib`, `yml`) with a subfolder per module, e.g. `language`, `parsing` (the cases
  of the frontend, e.g. `examples/dafny/parsing/globals_call.dfy` with
  `-print null` for its errors), `printing`, `vcgen`, `horn`, `teq`, `solver`,
  `simplify`, `hybrid`, and `transform`; one suite per language checks all of
  its examples ([Checked.scala](../test/src/cuvee/test/Checked.scala)).
  The translations of SV-COMP tasks (`benchmarks/sv-comp/dafny`) instead share one
  database of expected results, `benchmarks/sv-comp/dafny/expected.csv`, with the
  verdict of each task (safe or unsafe) and the number of remaining goals
  ([test/Database.scala](../src/cuvee/test/Database.scala)):
  `./Cuvee.sh -record <file> ...` prints rows, `./Cuvee.sh -test <db>.csv`
  checks all of them, and the suite `SVComp` runs only if the environment
  variable `CUVEE_SVCOMP` is set; likewise the algorithms of
  `examples/dafny/algorithms`, whose runs take minutes, only if
  `CUVEE_ALGORITHMS` is set (`Examples.excluded`), and the roundtrip suites
  of the printers (`Roundtrip` and `Programs`, every example printed and
  parsed back, `Examples.printing`) only if `CUVEE_PRINTING` is set, which
  a change of a parser or a printer requires. The C programs printed from these
  translations (`benchmarks/sv-comp/c`, by `-print c -known dfy,teq,rw`,
  those that parse again) have the same expected results, without times,
  in `benchmarks/sv-comp/c/expected.csv` (suite `SVCompC`), recorded before
  the programs were patched for other verifiers (see
  [benchmarks/sv-comp/c/README.md](../benchmarks/sv-comp/c/README.md)).
  The examples verified against a solver state `// expected: valid` or
  `// expected: invalid` in their second line.
- Relational tests run further commands on the accepted examples and print
  them: the printers must roundtrip (`Examples.roundtrip`), `-split`, `-flat`,
  and `-simplify` must keep the verdicts, and `-chc -z3` must agree with the
  second line.
- Unit tests build core terms directly where the command line cannot observe
  a property, e.g. the theories of `Context`, single rewrite steps, and the
  lemmas of `teq.dfy`.
- Hybrid programs and other inputs with polymorphic axioms are not passed to
  solvers; their tests generate the goals only.
- The tests of trace equation systems are listed in [teq.md](teq.md).
