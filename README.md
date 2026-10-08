# Cuvée

Cuvée is a pipeline for program verification in Scala 3. It reads SMT-LIB,
Boogie, Dafny, and C, translates them into one common representation of logic
and programs, transforms that representation, and prints it in any of these
languages or passes it to an SMT solver (z3 or cvc5).

## Capabilities

- **Frontends:** SMT-LIB 2 (`.smt2`, extended by procedures and programs),
  a subset of Boogie (`.bpl`), a subset of Dafny (`.dfy`), and simple
  integer programs in C (`.c`), with arrays as values and the verification
  conventions of SV-COMP, also given by SV-COMP task definitions (`.yml`)
  with a single input file; the sizes of integer types follow 32 or 64 bit
  Linux (`-arch 32|64`, by default 64, or the data model of the task). All are parsed into the same core, are type
  checked with polymorphism, and resolve overloaded arithmetic on `Int` and
  `Real`, and indexing of arrays and sequences. In Dafny, axioms, lemmas,
  and goals may be written `if φ then ψ` for `φ ==> ψ`, also below the
  quantifiers at the top, where `else` is optional.
- **Printers:** any input can be printed as SMT-LIB, Boogie, Dafny, or C
  (`-print smt2|bpl|dfy|c`), within the limits of each language, laid out
  for lines of 80 characters (`-linewidth <n>`).
- **Verification conditions** (`-verify`): weakest preconditions for
  procedures, covering:
  - contracts (`requires`, `ensures`, `modifies`) and `old(e)`;
  - loops with invariants, including `break`, `continue` and `return`;
  - termination measures (`decreases`);
  - global variables;
  - nondeterministic choice and iteration.
- **Trace equation systems** (`-teq`): verification conditions by symbolic
  execution, where each loop is summarized by a trace equation system: one
  trace per modified variable, `trace(e, for Y do x, y => u)`, and the
  constraint that all earlier iterations took a path through the body,
  `invs(for Y check y => φ)` (in Boogie `all(...)`), where the dependencies are traces without their
  last element, `⌊X⌋` in Dafny and Boogie (`butlast`, sort `Trace<T>`).
  Loop-free programs go directly to a solver,
  loops need rewriting by lemmas first: `-teq` injects a lemma database
  ([resources/cuvee/teq.dfy](resources/cuvee/teq.dfy)) once at the beginning
  of its output, whose rewrite rules `-simplify` applies, e.g. the counter
  lemma.
- **Constrained Horn clauses** (`-chc`): the same programs as Horn clauses
  for invariant inference. `-flat` then replaces record arguments of the
  predicates by their fields.
- **Monomorphization** (`-monomorph`): polymorphic functions are replaced by
  their instances, which the solvers require.
- **Splitting** (`-split`): goals and lemmas are split into individual
  obligations `forall xs. antecedents ==> conclusion`, which the solvers report
  one by one.
- **Simplifier** (`-simplify`): contextual simplification of formulas and
  simplification of programs, normalisation of arithmetic on `Int` and `Real`
  into polynomials, comparisons with positive coefficients, and derivatives.
- **Rewrite engine**: conditional rules `lhs = rhs if cond` from the
  assertions and lemmas with the attribute `:rw` (`axiom {:rw} φ`,
  `lemma {:rw} φ` in Dafny and Boogie, `(assert (! φ :rw))` in SMT-LIB), where
  `φ` is a universally quantified equation, equivalence, negation, or boolean
  atom, optionally with a premise as condition, and from function definitions
  with `:rw` whose body is a match on a parameter (one rule per case),
  applied by `-simplify` after each round,
  matching modulo associativity, commutativity, and 0 of `+` and `-`, and the
  binding structure of the trace combinators `trace`, `maps`, and `invs` from
  *Trace Equation Systems for Program Verification*; and Fourier-Motzkin
  elimination over the rationals.
- **Solvers** (`-z3`, `-cvc5`, `-timeout <ms>`): goals and lemmas are checked
  for validity, and assertions and `check-sat` are passed through. Lemmas
  with the attribute `free` (`lemma {:free} φ`) are assumed without proof,
  like axioms, although they are meant to follow from the theory.
- **Data types:**
  - integers, exact rationals for `real`;
  - arrays, sequences (`seq<T>`, using cvc5's `Seq` theory);
  - finite sets and multisets (`set<T>`, `multiset<T>`, using cvc5's `Set`
    and `Bag` theories) with literals `{a, b}`, `multiset{a, b}`, the
    operators `+`, `*`, `-`, `<=`, `<`, `in`, `!in`, `|s|`, and `m[x]`;
  - algebraic datatypes, tuples, and defined sorts;
  - bitvectors in SMT-LIB (`(_ BitVec n)`), with literals and all functions
    of the theory, and in Dafny (`bv8`, ...) with `+ - * / %`, `& ^ !`,
    unary `-`, unsigned comparisons, and `e as int`/`e as bv8`; numeric
    literals are bitvectors where the context requires it.
- **Hybrid programs** (Dafny syntax, after Platzer's dL):
  - differential equations with evolution constraints and differential
    invariants, `x', v' == v, -g && 0.0 <= x invariant ...;`;
  - derivatives `(x, v :: e)'`;
  - nondeterministic repetition, `while * { ... }`.

  Verification uses differential cuts and differential weakening (see
  [examples/dafny/hybrid/ball.dfy](examples/dafny/hybrid/ball.dfy)).
- **Parallel composition:**
  - methods may have assumption-commitment contracts (`assumes`, `commits`)
    over a global history of events, which `send` and `receive` extend;
  - these contracts are used by the parallel composition of calls,
    `parallel { p(a); x := q(b); }`;
  - `-hybrid` declares the channels, events, the history, `send`, and
    `receive` ([resources/cuvee/dafny/hybrid.dfy](resources/cuvee/dafny/hybrid.dfy)).

  See [examples/dafny/hybrid/par.dfy](examples/dafny/hybrid/par.dfy).

Known limitations and planned work are listed in [TODO.md](TODO.md).

## Usage

The build uses [mill](https://mill-build.org). z3 and cvc5 must be on the
`PATH` for `-z3`, `-cvc5`, and the tests.

```sh
mill -i run [options] file.{smt2,bpl,dfy,c} # run from source
mill -i test                                # run all tests
mill -i assembly                            # build out/assembly.dest/out.jar
./Cuvee.sh [options] file                   # run cuvee.jar, a copy of the assembly
```

Without options, the input is printed in its own language after parsing and
type checking. The transformations (`-verify`, `-teq`, `-chc`, `-flat`,
`-split`, `-monomorph`, `-simplify`) are applied in the order in which they
are given. The output options
(`-print`, `-z3`, `-cvc5`, `-o <file>`) apply to the result, wherever they
appear. For example:

```sh
mill -i run -verify -z3 examples/dafny/vcgen/max.dfy          # verify methods
mill -i run -chc -z3 examples/dafny/vcgen/max.dfy             # infer invariants
mill -i run -verify -simplify -z3 examples/dafny/hybrid/ball.dfy    # hybrid programs
mill -i run -verify -print smt2 examples/dafny/vcgen/max.dfy  # show the goals
mill -i run -teq examples/dafny/vcgen/sum.dfy                 # trace equation systems
mill -i run -teq -z3 examples/dafny/vcgen/max.dfy             # loop-free, by symbolic execution
mill -i run -chc -z3 examples/c/horn/count.c                       # C, invariants by Horn clauses
```

`-help` lists all options. `-debug simplify,rewrite` prints the steps of the
simplifier and of the rewrite engine that change an expression, in the
language of the output; `-debug solver` traces the communication with the
solvers.

## Documentation

- [doc/architecture.md](doc/architecture.md): the pipeline, the packages, and
  how a run flows through them.
- [doc/datastructures.md](doc/datastructures.md): the core representation of
  types, expressions, programs, commands, and the state.
- [doc/style.md](doc/style.md): coding style.
