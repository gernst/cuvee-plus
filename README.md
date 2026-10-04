# Cuvée

Cuvée is a pipeline for program verification in Scala 3. It reads SMT-LIB,
Boogie, and Dafny, translates them into one common representation of logic and
programs, transforms that representation, and prints it in any of the three
languages or passes it to an SMT solver (z3 or cvc5).

## Capabilities

- **Frontends:** SMT-LIB 2 (`.smt2`, extended by procedures and programs),
  a subset of Boogie (`.bpl`), a subset of Dafny (`.dfy`), and simple
  integer programs in C (`.c`), with arrays as values and the verification
  conventions of SV-COMP. All three are parsed into the same core, are type
  checked with polymorphism, and resolve overloaded arithmetic on `Int` and
  `Real`.
- **Printers:** any input can be printed as SMT-LIB, Boogie, Dafny, or C
  (`-print smt2|bpl|dfy|c`), within the limits of each language.
- **Verification conditions** (`-verify`): weakest preconditions for
  procedures, covering:
  - contracts (`requires`, `ensures`, `modifies`) and `old(e)`;
  - loops with invariants, including `break`, `continue` and `return`;
  - termination measures (`decreases`);
  - global variables;
  - nondeterministic choice and iteration.
- **Trace equation systems** (`-teq`): verification conditions by symbolic
  execution, where loops are summarized by trace equation systems with the
  combinators `trace`, `map`, and `all`, which a rewrite engine with lemmas
  simplifies (in progress).
- **Constrained Horn clauses** (`-chc`): the same programs as Horn clauses
  for invariant inference. `-flat` then replaces record arguments of the
  predicates by their fields.
- **Monomorphization** (`-monomorph`): polymorphic functions are replaced by
  their instances, which the solvers require.
- **Splitting** (`-split`): goals and lemmas are split into individual
  obligations `forall xs. antecedents ==> conclusion`, which the solvers report
  one by one.
- **Simplifier** (`-simplify`): contextual simplification of formulas and
  simplification of programs,
  normalisation of arithmetic on `Int` and `Real` into polynomials, and
  derivatives.
- **Solvers** (`-z3`, `-cvc5`, `-timeout <ms>`): goals and lemmas are checked
  for validity, and assertions and `check-sat` are passed through.
- **Data types:**
  - integers, exact rationals for `real`;
  - arrays, sequences (`seq<T>`, using cvc5's `Seq` theory);
  - algebraic datatypes, tuples, and defined sorts.
- **Hybrid programs** (Dafny syntax, after Platzer's dL):
  - differential equations with evolution constraints and differential
    invariants, `x', v' == v, -g && 0.0 <= x invariant ...;`;
  - derivatives `(x, v :: e)'`;
  - nondeterministic repetition, `while * { ... }`.

  Verification uses differential cuts and differential weakening (see
  [examples/hybrid.dfy](examples/hybrid.dfy)).
- **Parallel composition:**
  - methods may have assumption-commitment contracts (`assumes`, `commits`)
    over a global history of events, which `send` and `receive` extend;
  - these contracts are used by the parallel composition of calls,
    `parallel { p(a); x := q(b); }`.

  See [examples/par.dfy](examples/par.dfy).

Known limitations and planned work, including a C frontend, are listed in
[TODO.md](TODO.md).

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
type checking. The transformations (`-verify`, `-teq`, `-chc`, `-flat`, `-split`, `-monomorph`,
`-simplify`)
are applied in the order in which they are given. The output options
(`-print`, `-z3`, `-cvc5`, `-o <file>`) apply to the result, wherever they
appear. For example:

```sh
mill -i run -verify -z3 examples/vcgen/max.dfy              # verify methods
mill -i run -chc -z3 examples/vcgen/max.dfy                 # infer invariants
mill -i run -verify -simplify -z3 examples/hybrid.dfy       # hybrid programs
mill -i run -verify -print smt2 examples/vcgen/max.dfy      # show the goals
```

`-help` lists all options.

## Documentation

- [doc/architecture.md](doc/architecture.md): the pipeline, the packages, and
  how a run flows through them.
- [doc/datastructures.md](doc/datastructures.md): the core representation of
  types, expressions, programs, commands, and the state.
- [doc/style.md](doc/style.md): coding style.
