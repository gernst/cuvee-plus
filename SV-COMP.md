# SV-COMP tasks with the C frontend

A survey of what the C frontend cannot parse in the SV-COMP tasks linked from
`benchmarks/` (`ReachSafety-Arrays`, `ReachSafety-Loops`), via their task
definitions (`.yml`), and what the parser needs to accept them.

## Method

- Every task definition, except the verification witnesses in
  `*/witnesses/*.yml`, is run with `java -jar cuvee.jar -print c task.yml`.
  No solvers, no `-chc`, only parsing and resolution into core. The timeout
  is 30 s per run.
- Each input is run twice:
  - **raw:** the task as it is;
  - **stripped:** the input file without the SV-COMP harness, i.e. everything
    up to and including `void reach_error() ...`, with `ERROR:` labels
    removed and `__VERIFIER_assert(` replaced by `assert(`. Otherwise every
    task reports the same first error and hides everything after it.
- The tasks are run a few at a time per directory, 148 so far of 1397. Every
  directory has at least four tasks surveyed; all of `loop-acceleration` is
  done.
- In addition, a grep-based count over all 1397 inputs, after the harness,
  estimates how many tasks use each construct. The patterns are heuristics:
  the counts are approximate and a task can use several constructs.

The task set has 1397 tasks: 990 with a `.c` input and 407 with a `.i` input
(preprocessed). All have a single input file. 1193 have the property
`unreach-call`; the others only check e.g. `no-overflow`, `termination` or
`valid-memsafety`.

## Results

| | ok | error | timeout |
|---|---|---|---|
| raw (148 tasks) | 0 | 148 | 0 |
| stripped (148 tasks) | 67 | 81 | 0 |

- No run took longer than 0.8 s, so there are no timeouts. All errors are
  parse or resolution errors; there are no crashes, except scanner errors
  that are reported as `internal error` (see below).
- **No task parses as it is**, because of the harness alone. Without the
  harness, 45% of the sample parses.
- By the grep count, about 960 of the 1397 tasks (69%) use none of the
  constructs listed below after the harness, which is an upper bound for
  what harness support alone gains.
- The verification witnesses (`witnesses/*.yml`) are rejected cleanly by the
  yml frontend as "malformed task definition"; they are lists of
  invariant sets, not tasks.

## The SV-COMP harness (blocks every task)

Every input starts with the same declarations and definitions, which already
are builtins in the resolver (`Parser.builtin`), but the grammar does not
parse them:

```c
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_1-1.c", 3, "reach_error"); }

void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
```

In `.i` files, `reach_error` is the preprocessed `assert(0)`, and there are
more declarations from `assert.h`:

```c
extern void __assert_perror_fail (int __errnum, const char *__file, ...) __attribute__ (...);
extern void __assert (const char *__assertion, const char *__file, int __line) __attribute__ (...);
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "array_2-1.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
```

Older `.i` files spell `const` as `__const`.

What is needed:

1. **Pointer parameters and string literals in declarations of builtins.**
   `const char *` parameters, with or without names. Since only the
   signatures of builtins have them, the cheapest way is to parse pointer
   types (`typ ~ "*".*`) and string literals, and reject them in the
   resolver outside of builtins.
2. **`__attribute__ ((...))`** after declarators: skip a balanced
   parenthesized token sequence. `__extension__`, `__const` and
   `__inline`/`__restrict` can be dropped by the scanner (or treated as
   qualifiers).
3. **The bodies of builtins are not resolved,** so `reach_error` and the
   `.i` variant could be skipped syntactically: either a grammar rule that
   skips a balanced `{ ... }` body for functions named by `Parser.builtin`,
   or a lenient expression grammar (casts, `sizeof`, comma, `({ ... })`,
   `__PRETTY_FUNCTION__`). Skipping is much less work.
4. **Labels**, `ERROR: stmt` in `__VERIFIER_assert`: `id ":" stmt` in
   `stmt`, where the label is dropped (see `goto` below for labels that are
   used).
5. **`__VERIFIER_assert` is a builtin by name** (`__VERIFIER_` prefix), so
   its definition is filtered, but its calls end in "unknown function". It
   should be resolved like `assert`. In the examples (`examples/c`),
   `assert` is called directly, which is why this did not come up.

With 1–5, the stripped results above become the raw results.

## Constructs in the programs

Ordered by the number of tasks that use them (grep count over all 1397
inputs, after the harness), with where they occurred in the sample.

| Construct | Tasks | Example | Change |
|---|---|---|---|
| Casts | ~210 | `(long long) 2 * Y` (nla-digbench), `(signed long long) __VERIFIER_nondet_short()` (array-patterns) | Grammar: `"(" typ ")" expr` as a prefix operator in `atom`, before `parens(expr)`; to an integer type it is the identity on unbounded `Int` |
| Pointers, `&`, `*` | ~120–130 | `char *argv[]`, `char **argv` in `main` (loops), `void *malloc(unsigned int size)` (array-fpi, array-lopstr16) | Grammar: pointer declarators; parameters of `main` can be ignored. Pointer programs (memsafety, lists) need a heap model, which is a much larger step |
| `float`/`double` | ~130 | `float x = __VERIFIER_nondet_float();`, `1.0` (loop-floats-scientific-comp) | Scanner: float literals, the `.` is an unexpected character now; type `Real` or floating point; probably out of scope |
| `struct`/`union`/`enum` | ~95 | `struct S { int n; };` (array-industry-pattern, array-lopstr16), forward declarations `struct Velocity_Mode;` (loop-industry-pattern) | Grammar: struct declarations and member access `.`/`->`; resolution e.g. into datatypes or one array per field |
| `sizeof` | ~95 | mostly with `malloc` | Grammar: `sizeof(typ)`/`sizeof expr`, a constant per data model (ILP32/LP64 is in the task) |
| `malloc`/`alloca`/`free` | ~95 | array-fpi, array-memsafety | Dynamic arrays as values; for `int *a = malloc(N * sizeof(int))` an array of size `N` |
| `typedef` | ~90 | `typedef unsigned int size_t;` (`.i` headers, array-memsafety), `typedef struct { int n; } S;` | Grammar: `typedef typ id;` registers a type name; the grammar must know type names to parse `T x;`, so the scanner or parser needs a table (the usual C lexer hack) |
| `__attribute__`, `__extension__` | ~70 | also in `.i` headers | See the harness, item 2 |
| Hex literals | ~57 | `0x0fffffff` (loop-acceleration, loop-simple) | Scanner: `0[xX][0-9a-fA-F]+`; `Num` with the value converted |
| Bitwise and shifts | ~44 | `&` in `bAnd1.i` (array-crafted), `bin-suffix-5.c` (loop-invariants) | Scanner and grammar: `& \| ^ ~ << >>` with C precedences; resolution needs bit-vectors or uninterpreted functions on `Int` |
| `goto` and labels | ~42 | `goto END;` (loop-invgen), `main__loc: ;` in the CFA reducers (loop-invgen) | Grammar: `goto id;` and `id: stmt`; resolution into structured control flow is not generally possible: the CFA reducers are state machines of gotos |
| Integer suffixes | ~36 | `1L` (loop-acceleration `*_abstracted`), `0ULL` (loop-invariants64) | Scanner: `[0-9]+([uU]?[lL]{0,2}\|[lL]{1,2}[uU])`, the suffix is dropped |
| Multidimensional arrays | ~34 | `int A[n][m];` (array-multidimensional) | Grammar: `declarator` with several sizes; type `ArrayType(ArrayType(...))`, which `typ` already supports |
| Calls in loop conditions | ~30 | `while (__VERIFIER_nondet_bool())` (loop-zilu), `__VERIFIER_nondet_uint()` (loop-invariants) | Resolver: evaluate the call before the loop and at the end of the body, or desugar to `while (1) { c = f(); if (!c) break; ... }`; parses already |
| Calls in `&&`/`\|\|` | few | `x && __VERIFIER_nondet_int()` (loop-lit `afnp2014`) | Resolver: short-circuit as an `if`; parses already |
| Char and string literals | ~21 | mostly in harness-like code | Scanner: `'c'` as its code, strings only for builtins |
| Initializer lists | ~19 | `int A[2048] = { 0 };` (loop-acceleration `*-simple`) | Grammar: `"{" expr ~* "," "}"` in `declarator`; resolution as `const`-array plus stores |
| `switch` | ~10 | | Grammar and resolution into `if` chains (with fall-through) |
| Chained assignment | ~5 | `i = k = 0;` (loops-crafted-1 `iftelse`) | Grammar: assignment as an expression, or `assign` with a right-hand side that is an assignment |

## Other observations

- **Scanner errors are internal errors.** An unexpected character (`&`, `.`)
  throws a `RuntimeException` in `Scanner.flex`, which is reported as
  `"internal error" "RuntimeException" "unexpected character '&' at 8:14"`.
  It should be a regular parse error via `Error.raise`.
- **Integers are unbounded.** All integer types are `Int`, so unsigned
  wrap-around and overflow are not modelled. Some tasks rely on them, e.g.
  `overflow_1-1.c`, and tasks with `unsigned` loop counters that wrap; their
  verdicts would differ even once they parse. The data model of the task
  (ILP32/LP64) is read by the yml frontend, but not used.
- **Properties.** The frontend ignores the property of the task. Tasks
  without `unreach-call` (204) check other properties (`no-overflow`,
  `termination`, `valid-memsafety`), which the translation does not
  express.
- **Error messages of the parser.** The path in a parse error
  (`List(unit, top, function, ...)`) grows with the nesting, e.g. hundreds
  of entries for the nested `if`s of the CFA reducers. Showing only its last
  few entries would make the errors readable.

## Suggested order

1. The harness (items 1–5), which turns 0% into roughly 45% (sample) to
   69% (upper bound). **Done** (branch `c`): pointer types in signatures
   (rejected by the parser outside of builtins), parameters without names,
   string literals in the scanner, `__attribute__`, the GCC spellings
   `__const`, `__inline`, `__restrict`, `__extension__`, the bodies of
   builtins skipped, labels dropped, `__VERIFIER_assert` as `assert`
   (example `examples/c/harness.c`).
2. Literals: hex, integer suffixes, chars; scanner errors as parse errors.
   **Done:** decimal, octal and hexadecimal constants with suffixes,
   character constants with escapes (`Parser.literal`), unexpected
   characters as errors (`Syntax.error`); also `float`/`double` in the
   signatures of builtins such as `__VERIFIER_nondet_double`, rejected by the
   parser otherwise, like pointers.
3. Casts to integer types, multidimensional arrays, initializer lists,
   chained assignment. **Done:** casts to integer types are the identity,
   to `_Bool` a comparison with zero, others are rejected; arrays of arrays
   with updates of nested elements; initializer lists of local and global
   arrays, whose missing elements are zero; `x = y = e` is `y = e; x = y`.
4. Calls in loop conditions and in `&&`/`||` (resolver only).
5. `typedef` of integer types (the `.i` headers), `sizeof` as a constant of
   the data model.
6. Beyond integer programs with arrays: structs, pointers and `malloc`,
   floats, bitwise operators, `goto`; these need decisions about the
   semantics, not only the grammar.
