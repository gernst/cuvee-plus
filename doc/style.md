# Coding Style

## Format

- avoid curly braces: use Scala 3 indentation syntax, also for partial
  functions and lambdas passed as the last argument, `xs.map: x =>` and
  `xs.collect:` followed by `case` lines; companion objects and classes end
  without braces as well
- imports name one member per line or use a wildcard, no braces
  (`import cuvee.verify.Horn`, `import easyprint.Doc._`), renames with `as`
- always add newline after `def f(...) =`
- add blank line between cases unless very compact
- introduce updated variables `x_` before constructing new objects
- `if c then a else b` on separate lines (`if`, `then`, `else`), except for
  very short expressions
- `for ... yield` with the generators on their own lines when there are
  several, `for x <- xs yield e` on one line otherwise
- align the arrows of compact `match` expressions whose cases fit on one line

## Naming

- an updated or derived value of `x` is `x_`, further ones `x__`; the inputs
  of a function keep their names, the results get the suffix
- the values of variables at other points of a program are named after them:
  `gs_` for the global variables at the entry of a procedure, `xs_` for fresh
  copies, `mod0` for values kept apart
- names of core functions follow SMT-LIB where it has them (`select`,
  `seq.nth`, `div`), the frontends translate their own names onto these
- sugar objects for built-in functions are named after the operation, except
  for those of a type, which are grouped in an object named after it in the
  plural: arithmetic per numeric type, `Ints.plus`, `Reals.lt`, `Ints.zero`,
  `Ints.ring`, the functions on sequences as in `Fun.seq`, `Seqs.len`,
  `Seqs.nth`, since e.g. `Unit` would shadow a Scala name, and the
  constructors of the datatypes of teq.dfy, `Nats.succ`, `Lists.nil`,
  `Traces.step`, and of tuples, `Tuples(args)`
- avoid shadowing Scala names in `core`, e.g. no case class `Map` (hence
  `Maps`)

## Parameters

- functions that need context take it first, in a fixed order:
  `(config, state, ctx, ...)` in the simplifier and the rewrite engine,
  `(state, scope, ...)` in type checking, `(config, state, prefix, cmds, last)`
  for transforms
- recursion threads the context explicitly instead of global or mutable state;
  mutable state is local to a class that represents a pass, e.g. the `state`
  of a parser, or shared deliberately, e.g. the step budget of the rewrite
  rules (`Context.steps`)
- overloaded methods of the same name for the different syntactic categories,
  e.g. `simplify` for commands, attributes, programs, and expressions, or
  `lines` and `doc` in the printers

## Errors

- check preconditions with `Error.report(msg, info*): require(...)`, which
  reports the message together with the relevant values
- raise errors with `Error.raise(msg, info*)` for unsupported or invalid input,
  never with exceptions of the standard library
- messages are short, lowercase phrases, e.g. "type mismatch",
  "operator not defined for type", which tests compare literally

## Core representation

- all data structures are immutable case classes, sealed traits for the
  syntactic categories, so that pattern matches are checked for exhaustiveness
- the classes do not check their consistency when they are constructed or
  queried; the parsers and builders check the input instead, e.g. type checking
  rejects map without update, and `Rule.check` the rules from the input
- build expressions and programs in the frontends through the builders
  `state.exprs`, `state.progs`, `state.types`, and `state.cmds`, which look
  up declarations and instantiate type parameters freshly
- use the sugar objects (`And`, `Eq`, `Ints.plus`, ...) to build and match
  applications of built-in functions instead of spelling out `App`
- recurring operations on lists of core terms are extension methods in
  [Sugar.scala](../src/cuvee/core/Sugar.scala), e.g. `phis.conjuncts` and
  `phis.disjuncts` (flattened, without neutral elements and duplicates)
- in the simplifier, results are built with the normalizing helpers
  (`not`, `and`, `or`, ...) rather than the constructors, and each helper
  covers its own constructor only; what the traversal already decides is not
  checked again
- substitutions (`Subst`) avoid capture under binders; fresh variables come
  from `x.fresh`
- built-in functions in `Fun` and the declarations of the preludes coincide,
  with type parameters `a₀, a₁, ...` and formal parameters `x₀, x₁, ...` in
  the notation of each language

## Comments

- every non-trivial definition gets a comment that explains its purpose and,
  where relevant, the reasoning or the source (e.g. a definition of the paper
  on trace equation systems), in lowercase prose without a trailing period
- comments explain why and what holds, not how the code proceeds step by step
- limitations go into [TODO.md](../TODO.md) rather than into comments, with a
  link to the file

## Tests and examples

- every feature comes with tests: unit tests on core terms, and examples in
  `examples/<language>/` that the tests run through `cuvee.Cuvee.run`
- every example states its command line in its first line, e.g.
  `// ./Cuvee.sh -vcgen -z3 examples/dafny/vcgen/abs.dfy`, with its expected
  output in `name.out` and `name.err` (see [architecture.md](architecture.md));
  tests never write files
- verification examples state their expected verdict in the second line,
  `// expected: valid` or `// expected: invalid`
- an error test checks the exact message of the error

## Commits

- commit once a step compiles and all tests pass, with a message of the form
  `area: what changed; ...` and the version number in `Config.version`, whose
  second digit counts major features and whose third digit counts minor ones

## Context

All code must have at all times access to context like the current script,
the current state, the current scope (type parameters + variables), etc.
