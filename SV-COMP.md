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

### After steps 1–5 (branch `c`, version 0.19.7)

The same 148 tasks, as they are:

| | ok | error | timeout |
|---|---|---|---|
| before | 0 | 148 | 0 |
| after | 109 | 39 | 0 |

The remaining errors in the sample: libc headers with structs, unions,
`long double` and prototypes with pointers (`stdlib.h`, 6 tasks, plus
`__bswap_32` with `__builtin_bswap32`, 2), structs (12), floating point
(4), bitwise `&` (5), `goto` in the CFA reducers of `loop-invgen` (5),
pointers to pointers (1), `switch` (1), and increments inside expressions
(4).

Increments inside expressions, e.g. `while (counter++ < 10)`, were missed
by the first survey: they occur in about 260 tasks, nearly all of
`nla-digbench-scaling`. **Done:** `x++`, `x--`, `++x`, `--x` in
expressions, whose updates are made before the expression, like calls, and
whose value is the old one for the postfix forms.

The sizes of integer types follow the data model: `-arch 32|64` (ILP32 or
LP64, by default 64), which the yml frontend sets from the `data_model` of
the task.

### All tasks (version 0.19.12)

All 1397 tasks, each parsed with `java -jar cuvee.jar task.yml -o /dev/null`,
four at a time, with a timeout of 30 s: **1167 parse (84%), 230 fail, no
timeouts**; the slowest task takes 2.8 s (with four runs in parallel).

| Directory | ok | tasks |
|---|---|---|
| array-cav19 | 13 | 13 |
| array-crafted | 28 | 43 |
| array-examples | 92 | 96 |
| array-fpi | 151 | 151 |
| array-industry-pattern | 8 | 17 |
| array-lopstr16 | 1 | 11 |
| array-memsafety | 0 | 65 |
| array-memsafety-realloc | 0 | 3 |
| array-multidimensional | 20 | 20 |
| array-patterns | 37 | 37 |
| array-programs | 16 | 16 |
| array-tiling | 27 | 29 |
| loop-acceleration | 44 | 44 |
| loop-crafted | 7 | 9 |
| loop-floats-scientific-comp | 0 | 7 |
| loop-industry-pattern | 2 | 18 |
| loop-invariants | 9 | 10 |
| loop-invariants64 | 1 | 1 |
| loop-invgen | 8 | 29 |
| loop-lit | 27 | 33 |
| loop-new | 8 | 11 |
| loops | 57 | 77 |
| loops-crafted-1 | 53 | 55 |
| loop-simple | 8 | 8 |
| loop-zilu | 57 | 58 |
| nla-digbench | 54 | 57 |
| nla-digbench-scaling | 439 | 479 |

The 230 failures need the constructs of step 6, which need decisions about
the semantics:

- libc headers (`stdlib.h`, e.g. `long double strtold`), 60, all in the
  memory safety tasks (`array-memsafety*`), whose property is not
  `unreach-call`;
- floating point, 50 (`nla-digbench-scaling` with `double`, 40,
  `loop-floats-scientific-comp`);
- structs, about 40 (`loop-industry-pattern`, `array-lopstr16`,
  `array-industry-pattern`, `loops`);
- `goto`, about 25, the `*-reducer` variants of `loop-invgen`, `loop-lit`,
  `loop-new`, `loop-crafted`, which are state machines of gotos;
- bit-level operations (`&`, `|`, `^`, `>>`), about 25, not to be supported;
- pointers other than allocated arrays, about 15, e.g. arrays of pointers
  to separately allocated cells (`int *a[N]; a[i] = malloc(sizeof(int))`);
- `__bswap_32` of `stdlib.h` with `__builtin_bswap32`, 4, not to be
  supported.

The comma operator (`i = 0, j = 0`, also in `for` loops) was missing too
and is supported now.

### Trace equation systems

`-teq` succeeds on all C examples and on ten tasks that use the new
constructs (calls in loop conditions, multidimensional arrays, `malloc`,
increments in expressions, `continue`, hexadecimal constants), in about
3 s each, e.g. `array-fpi/brs1`, `nla-digbench-scaling/ps6-ll_unwindbound20`,
`array-multidimensional/copy-3-n-u`, `loop-zilu/benchmark01_conjunctive`.
Its output is not C, so `-print c` omits it; use `-print smt2` or
`-print dfy` to see it.

### The fallback encoding (version 0.35.2, October 10, 2026)

`xml/cuvee-fallback.xml` passes `-teq -simplify -split -simplify -fallback
-z3` (see [doc/teq.md](doc/teq.md)), with the limits of the other tools
(15 min, 2 cores, 7 GB), z3 limited by the time limit only
(`-timeout 900000`), and shipped next to the jar, since the machines of the
cluster have none. Goals that z3 does not prove are `unknown`
([cuvee.py](cuvee.py)), since the encoding generalizes the functions of
`teq.dfy` that it does not define. The baselines are those of
`-teq -simplify -split -simplify` of October 9 (1 core).

| Category | baseline 1 min | fallback 1 min | baseline 15 min | fallback 15 min |
|---|---|---|---|---|
| Loops (758) | 119 | 207 | 120 | 219 (+99, none lost) |
| Arrays (440) | 107 | 116 | 107 | 116 (+9, none lost) |

- The new proofs are in all folders of Loops (`loop-zilu`, `loop-invgen`,
  `loop-lit`, `loops`, `nla-digbench`, ...), where the simplifier left a
  residual goal, in Arrays in `array-cav19` and `reducercommutativity`.
- Incorrect true: 15, `nla-digbench/geo1-u` and its scaled variants, which
  fail only by the overflow of `unsigned long long`; the C frontend models
  unsigned integers as unbounded, hence the goal holds. A first run had 16
  more in `array-fpi` and `array-patterns`, from a vacuous definition of
  `consts` in `-fallback` (fixed in 0.35.1).
- 15 min instead of 1 min adds 12 proofs in Loops and none in Arrays: of the
  runs that reach the minute, 110 end later by `rewriting does not
  terminate`, 58 in Arrays still reach 15 min in z3.
- Errors at 15 min: in Loops, `rewriting does not terminate` 140, the
  unsupported `term with free sequences` 41 and `the length of a trace or
  list is unknown` 28 of `-fallback`, `type mismatch` 40, floating point 29,
  `solver error` 25; in Arrays, the length unknown 50, free sequences 27,
  `rewriting does not terminate` 17, parse errors 17, `solver error` 16.
- `solver error` (all 41): `unknown constant n$..` of z3. A combinator that
  is not equated to a variable, e.g. `maps(for ⌊K⌋, ... )` among the
  dependencies of a trace, became a fresh function of the free variables of
  the term, defined in the antecedent of the goal, but its length `n` comes
  from the counter `K == counter(0, 1, n)` and was not among them, hence
  unbound in the definition. Likewise, the generalized functions of
  `teq.dfy`, e.g. `count(c, maps(for ⌊K⌋ ...))`, did not depend on `n`, so
  that two counts of the same array of different lengths were the same.
  Fixed: the arguments include the free variables of the lowered functions
  and lengths of the traces of the term (`Fallback.arguments`, tests
  `examples/c/teq/fallback.c` and `examples/dafny/teq/fallback_count.dfy`);
  the tasks are `unknown` now, e.g. `Sat` for `bresenham-ll`, `mannadiv`,
  and `apache-escape-absolute`, through the generalized `count`.
- `type mismatch` (39 of 40, `divbin`, `divbin2`, `hard-ll`, `hard-u`,
  `hard2`, `dijkstra-u` of `nla-digbench-scaling`): the goal after
  `-simplify` is ill-typed, `-fallback` only checks it. In loops
  `while (counter++ < 1)` after another such loop, the counter starts at 2,
  so that all guards of the updates are false and `Simplify` drops all
  cases, an update without cases, `Eps(Nil)`. `Rewrite.matches` covers each
  case of the update of the expression by a case of the pattern, vacuously
  if there is none, also for patterns that are no updates (the case
  `(_, Eps(updates_))`), so that every rule matches `Eps(Nil)` without
  instantiating its variables; the first rule tried replaces it, here
  `truth(x) = x != 0` of the C prelude, e.g.
  `B == trace(b, for ⌊K⌋, ⌊Counter⌋ do b, k, counter :: x != 0)` of type
  `Trace<int>`. Confirmed by `(= (eps ((< a a) 3)) 5)` with the rule
  `f(x) = x + 1`, which `-simplify` turned into `(= x 4)`. Fixed: an
  update without cases is `unspecified` of `teq.dfy`, and `Rewrite`
  reports variables of a rule that a match leaves unbound as an error;
  `divbin_unwindbound1` and `dijkstra-u_unwindbound1` are proved,
  `hard-u_unwindbound1` (unsafe) is not.
- The remaining `type mismatch`,
  `loops/veris.c_sendmail_tTflag_arr_one_loop`, also in the baseline, was
  the assignment `s = in` of an array to a local pointer that is never
  read. Fixed: assignments to local pointers that are never read are
  dropped, except for the effects of their values
  (`examples/c/parsing/unread_pointer.c`); the task is proved.

### Other verifiers on the C versions of the local benchmarks (October 10, 2026)

The C programs of `benchmarks/sv-comp/c`, printed from the Dafny translations
and patched with the SV-COMP harness and sized arrays (see its
[README](benchmarks/sv-comp/c/README.md)), 646 tasks without the 5 whose
translation loses an update of an array parameter, task set
`C.unreach-call.Unbounded` of `xml/*.xml`, 5 min per task (`-T 300s`), 2
cores, each tool started from its directory:

| tool | correct true | correct false | wrong true | wrong false |
|---|---|---|---|---|
| Cuvée (0.35.15) | 211 | – | 0 | 0 |
| Cuvée+Z3 (`-fallback`) | 256 | – | 1 | 0 |
| Korn | 161 | 96 | 1 | 5 |
| CPAchecker | 93 | 143 | 0 | 46 |
| AISE | 215 | 101 | 55 | 36 |
| Symbiotic | 165 | 95 | 57 | 27 |
| UAutomizer | 176 | 144 | 2 | 26 |

The wrong results are mostly due to the tasks, not the tools: the C programs
do not always mean what their Dafny sources and expected verdicts say.

- Uninitialized locals: 132 functions declare `N` (or other variables)
  without assigning them, which is an arbitrary value in Dafny and undefined
  in C. The tools based on KLEE (Symbiotic, AISE) use a fixed value instead,
  so that the violation is unreachable: 55 of the 57 wrong true results of
  Symbiotic and 53 of the 55 of AISE are in such files. Proposal: assign the
  variables that Dafny leaves arbitrary a nondeterministic value in the C
  versions (`N = __VERIFIER_nondet_int();`), in `arrays.py` for `N`, in
  general for every local that is read before it is written.
- Overflow: the translations compute with unbounded integers and drop the
  bounds of at least 100, also those on values that rule out an overflow in
  the original task, e.g. `assume_abort_if_not(a[i] < 10000 && a[i] >
  -10000)` of `array-cav19/array_min_and_copy_shift_sum_add`; the C versions
  overflow (undefined), which the bit-precise tools find, e.g. most of the 46
  wrong false of CPAchecker (not all checked); `nla-digbench/geo1-u` is
  unsafe only by the wrap-around of `unsigned long long`, which Cuvée and
  Korn prove safe. Proposal: keep the bounds on values in the C versions (or
  in the translations, where they are harmless), or determine the expected
  verdicts of the C versions separately.
- Symbolic bounds: where an assertion depends on the bound, the verdict of
  the original task does not hold for an arbitrary one, e.g. `j < N / 8` of
  `array-programs/partial_mod_count_4`, `_5`, `_limited_2`, `_limited_5`
  fails for small `N`, and `loop-zilu/benchmark52_polynomial` (`N` for 100).
  These are wrong in the Dafny tasks as well. Proposal: keep the constant
  where an assertion depends on it, or correct the expected verdict.
- AISE reports 36 violations of safe tasks, 21 in programs whose arrays have
  a fresh size `N` and 12 with the program's own `N`: to be checked, possibly
  accesses beyond the size or the contents of uninitialized arrays, which are
  arbitrary in Dafny.
- Excluded: `array-examples/data_structures_set_multi_proc_ground-1`, `-2`,
  `_trivial_ground`, `sanfoundry_43_ground`, and
  `array-industry-pattern/check_removal_from_set_after_insertion` update an
  array parameter only in a local copy (see the README of the C versions).

Since then (October 11, 2026), the C versions follow these proposals:

- [nondet.py](benchmarks/sv-comp/c/nondet.py) initializes the locals by
  nondet calls.
- [sizes.py](benchmarks/sv-comp/c/sizes.py) bounds the sizes of the arrays
  below 2^31 bytes.
- The tasks that other verifiers rightly find false assume the conditions
  under which the property holds, as their Dafny translations do now; the
  bounds that kept the arithmetic within `int` were removed again (October
  12, 2026), since the tasks are meant for verifiers that treat the
  arithmetic of C as unbounded.
- The 5 tasks that pass an array to a function that changes it are removed
  (October 12, 2026), 646 remain.

[false-verdicts.md](benchmarks/sv-comp/c/false-verdicts.md) has the analysis
of the 72 wrong false verdicts and the fixes.
[c_patches.diff](benchmarks/sv-comp/dafny/c_patches.diff) has all the
changes. The results above predate these changes.

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
- **Integers are unbounded.** All integer types are `Int`; without
  `-unbounded`, unsigned integers wrap around by the overflow functions of
  the prelude (`uint(x) = x mod 2^32`, ...) and nondeterministic values are
  within the ranges of their types, but signed overflow is not modelled. Some tasks rely on them, e.g.
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
   (example `examples/c/vcgen/harness.c`).
2. Literals: hex, integer suffixes, chars; scanner errors as parse errors.
   **Done:** decimal, octal and hexadecimal constants with suffixes,
   character constants with escapes (`Parser.literal`), unexpected
   characters as errors (`Syntax.error`); also `float`/`double` in the
   signatures of builtins such as `__VERIFIER_nondet_double`, rejected by the
   parser otherwise, like pointers; float literals, `&x`, and `*p` are
   parsed and rejected with "not supported".
3. Casts to integer types, multidimensional arrays, initializer lists,
   chained assignment. **Done:** casts to integer types are the identity,
   to `_Bool` a comparison with zero, others are rejected; arrays of arrays
   with updates of nested elements; initializer lists of local and global
   arrays, whose missing elements are zero; `x = y = e` is `y = e; x = y`.
4. Calls in loop conditions and in `&&`/`||` (resolver only). **Done:**
   the calls of a loop condition are made at the beginning of each
   iteration, which is left if the condition is false (`Parser.guard`); the
   right operand of `&&`/`||` is evaluated in an `if` into a temporary.
5. `typedef` of integer types (the `.i` headers), `sizeof` as a constant of
   the data model. **Done:** the scanner replaces the names of types by
   their definitions (`Typedefs`), the grammar skips typedef declarations,
   so a typedef of e.g. a struct fails only where it is used; `sizeof` of
   integer types, where `long` is an error, as its size depends on the data
   model, which the yml frontend does not pass on; `sizeof` of expressions
   by the declared integer type and array sizes of their variables, e.g.
   `sizeof(array)` of `char array[1024 * 100]`, otherwise by their type. The tasks with typedefs
   now fail later, at structs and pointers (6.), or at functions of the
   headers that are never called, e.g. `__bswap_32` with
   `__builtin_bswap32`, and prototypes with pointers.
   **Also done:** allocations of arrays, i.e. local pointers initialized
   by `malloc`/`alloca` of `sizeof(T) * n` or `calloc(n, sizeof(T))`, with
   optional casts, are arrays of `T`, whose elements are arbitrary, or zero
   for `calloc`; `free` is skipped; other pointers are rejected. This covers
   e.g. `array-fpi`.
6. Beyond integer programs with arrays: structs, pointers and `malloc`,
   floats, bitwise operators, `goto`; these need decisions about the
   semantics, not only the grammar.
