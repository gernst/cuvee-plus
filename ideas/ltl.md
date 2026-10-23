# Linear temporal specifications by weakest preconditions

A plan to implement the calculus of "Weakest Precondition Rules for Programs with Linear Temporal Specifications"
(ISoLA 2026, `isola2026.pdf`) in the Dafny frontend and in `-vcgen`. The core case `Prop` and its syntax in Dafny and
SMT-LIB (steps 1 and 2 of the plan) are implemented, documented in [datastructures.md](../doc/datastructures.md)
and [architecture.md](../doc/architecture.md); the rest is not (Oct 19, 2026).

## The paper in Cuvée's terms

- **Programs** are `κ ::= φ | c; κ | ω(x)`: a command is always followed by a continuation, either a formula
  `φ` (an assumption about the rest of the trace), or a placeholder `ω(x)` (an abstract set of traces over
  `x`). Iteration is `iterℓ(c)`; `while b` and `if` are derived from `assume`, which is an atomic action and
  takes a step.
- **Judgement:** `{α} c; κ {γ}` iff `(c; κ) ⊨ α ⇒ γ`, over infinite traces only. `wp(κ | ψ)` is the formula
  `κ ⇒ ψ`.
- **Rules** (Algorithm 1), forward through the program, where the guarantee travels with the execution:
  - `wp(φ | ψ) = φ ⇒ ψ` (2); choice is a conjunction (3); sequences reassociate (4);
  - an atomic action steps, `∀x'. step(A, x, x') ⇒ wp(κ' | unfold(ψ, x, x'))` (5), where `unfold`
    (Algorithm 2) splits `ψ` into its current-state part over `x` and its next-state part, shifted onto `x'`
    by the expansion laws (`□φ ≡ φ ∧ ◦□φ`, ...);
  - a loop with the annotation `ℓ ↦ (ι, H)` gives `(ι ⇒ ψ) ∧ ∀x. wp(κ | ι) ∧ ∀x. wp(c; ω(x) | H(ω(x)) ⇒ ι)`
    (6), with `x = mod(c)` and a fresh placeholder `ω`.
- **Hypothesis operators** `H` (Definition 4) carry the (co)induction principles:
  - well-founded `Mδ(τ) = ∃z. z = δ ∧ □(δ < z ∧ τ ⇒ ι)` (Lemma 1);
  - induction from an assumption, `I♢φ⇒γ(τ) = φ R⁺ (τ ⇒ γ)`, and coinduction for a guarantee,
    `Cα⇒□φ(τ) = ¬(φ W⁺ (α ∧ τ))` (Lemma 2), with the strict operators
    `φ W⁺ ψ ≡ φ ∧ ◦(ψ ∨ φ W⁺ ψ)` and `φ R⁺ ψ ≡ φ ∨ ◦(ψ ∧ φ R⁺ ψ)`;
  - composed by `(H₁ ▷ H₂)(τ) = H₁(τ) ∧ H₂(τ ∧ H₁(τ))` (Lemma 3), e.g. `C ▷ M` for `□♢prime(x)`.
- **The goals** are temporal implications for an oracle. In the examples of the paper they close by one-step
  reasoning: the placeholder and the strict operators are unfolded far enough that the remaining temporal
  subformulas match as atoms.

## What Cuvée has already

- `Iter(body, attrs)` (`while *`) and `While` with `invariant` and `decreases`, in the frontend and the core
  ([hybrid.md](../doc/hybrid.md)).
- The precedent of `-hybrid`: a module injected into Dafny input
  ([hybrid.dfy](../resources/cuvee/dafny/hybrid.dfy)), method clauses `assumes` and `commits` stored as
  procedure attributes, read by `Attrs.assumes`/`Attrs.commits`, printed by the Dafny printer and read back by
  the SMT-LIB parser.
- `Old.elim` to rigid entry values, `VCGen.decreases` for the lexicographic order of `decreases`.
- `VCGen.wp` goes **backward** (`foldRight` over a postcondition, `Assign` by substitution). Neither is
  sound for temporal guarantees: the substitution `x := e` inside `□φ` changes the formula at all future states.
  The temporal rules therefore need a forward generator of their own.

## Core: `Prop`

Temporal formulas are a core case next to `Old` and `Diff`, which are core cases because they are not functions
either:

```scala
// a temporal operator applied to formulas, or a placeholder (a fresh name) applied to the state variables;
// not a function: always(p) is not determined by the value of p now
case class Prop(op: Name, args: List[Expr]) extends Expr   // typ Bool
```

- **Operators** `Prop.ops`, by name and arity, on `Bool`: `next`, `always`, `eventually` (unary), `until`,
  `unless` (W), `release`, and the strict `until+`, `unless+` (W⁺), `release+` (R⁺) (binary), which expose
  their left operand for at least one step, `φ U⁺ ψ ≡ φ ∧ ◦(ψ ∨ φ U⁺ ψ)` as a least fixpoint. The core names are those of the
  Dafny syntax, so `translate` needs no entries.
- **Placeholders** `ω` are `Prop`s whose `op` is a fresh name (`Name("ω", Some(k))`, not among `Prop.ops`),
  applied to the state variables (of any type). No declarations, no attributes: the generator creates them,
  and the lowering treats every `Prop` as an atom by its syntax, so `ω(x') ∧ x' = x''` never gives `ω(x'')`.
- **What changes** (the places that handle `Old` and `Diff`, about 15 small edits):
  - `Expr.scala`: the case, `params`/`free`/`funs` of the arguments, `typ = Bool`, one line in `map`;
  - `Subst`: one line into the arguments. This is correct for renaming, which is all the temporal generator does.
    The backward `x := e` of `VCGen.wp` never sees temporal methods (a comment at the case says so);
  - `Type.check` (operators: `Bool` arguments; placeholders: any) and `Type.expand`;
  - `simplify/Simplify` and `prove/Simplify`: the arguments without the facts of the context, which hold now
    only (the engines do not know which variables are flexible). `Normalize.lift`
    stops at it already (only `App` arguments are searched for `ite`), and so does `-split`;
  - printers: Dafny and SMT-LIB (`(always φ)`, `(ω$3 x y)`); Boogie, C, and Lean reject it, like `Diff`;
  - z3 rejects the undeclared operators, so an unlowered goal never reaches a solver by accident.

## Dafny frontend

**Operators in the mixfix tables.** Prefix operands are parsed at the operator's own precedence
(`Mixfix.prefix_app`):

| | operators | precedence | |
|---|---|---|---|
| prefix | `next`, `always`, `eventually` | 5 | operand down to comparisons: `always x >= 0 && p` is `(always (x >= 0)) && p` |
| infix | `until`, `unless`, `release`, `until+`, `unless+`, `release+` | 4, right-associative | between `&&` (3) and the comparisons (5): `always p until q` is `(always p) until q`, `p until q until r` is `p until (q until r)` |

- The words are `sym` tokens matched by `Mixfix` by their text, like `in`, so the scanner needs no
  keywords. Only `until+`, `unless+`, and `release+` need a scanner rule (part of `sym`, which wins by the
  longest match), since `+` is a token of its own. The words become reserved: they occur only
  in comments of the existing `.dfy` files.
- `!always p` does not parse, since `!` (9) admits no operand of lower precedence. It is written
  `!(always p)`, and the printer parenthesizes it so.
- `Parser.resolve` turns `App(op, args)` with `op` among `Prop.ops` into `Prop`. Placeholders print as
  `ω₃(x, y)`: `ω` becomes a character of `sym` in the Dafny and SMT-LIB scanners, and the parsers resolve an
  application of an indexed `ω` that is not declared to a placeholder, so that printed goals parse again.

**Clauses**

- Method clause `guarantees γ` (after `ensures`, before `assumes`). A method with at least one `guarantees` is
  **temporal**, and `-vcgen` verifies it by the rules below. `requires α` may then be temporal as well, since
  a state precondition is the special case of `α` at the initial state; the guarantee of the method body is
  `ψ = requires ⇒ guarantees`. `ensures` keeps its meaning: it is checked when the method terminates.
- Loop clauses, after `invariant`:
  - `guarantees ι`, the generalization of the paper. The default is `invariants ⇒ ψ` for the guarantee `ψ`
    current at the loop, which is the choice of both examples of the paper.
  - The hypotheses `coinduction` (`C`, needs `ι` of the shape `α ⇒ always φ`) and `induction` (`I`, needs
    `eventually φ ⇒ γ`). The generator reads the shape off `ι`, with the antecedent as a conjunction from
    which it picks the `eventually` conjunct, and reports an error otherwise.
  - `decreases δ` is `M` in a temporal method: induction becomes available where `δ` has decreased, with
    the lexicographic order of `VCGen.decreases`. It is not a termination obligation.
  - Composition `▷` in the order of the clauses; `decreases` comes last in the grammar
    (`invariant* guarantees* (coinduction | induction)* decreases*`), so `C ▷ M` as in Example 4.
- Core: attributes `guarantees` (`Expr`), `coinduction`, `induction` (no value) of `DefineProc`/`While`/`Iter`,
  plus an accessor `Attrs.guarantees`, as for `assumes`. New keywords in `Scanner.flex`: `guarantees`,
  `coinduction`, `induction`.
- Printers: Dafny prints the clauses (roundtrip, `CUVEE_PRINTING=1`); the SMT-LIB parser resolves
  `:guarantees` as a formula, like `:assumes`; Boogie, C, and SV-LIB reject them.
- No option `-ltl` and no injected module: the operators are always part of the Dafny frontend, like
  derivatives.

Example 1 of the paper (inputs are fixed in Dafny, hence a global variable):

```dafny
// ./Cuvee.sh -vcgen -print dfy examples/dafny/ltl/primes.dfy
predicate prime(n: int)
function delta(x: int): int
lemma delta_decreases(n: int) requires !prime(n) ensures 0 <= delta(n + 1) < delta(n)

var x: int

method primes()
  modifies x
  requires x >= 0
  guarantees always eventually prime(x)
{
  while true
    invariant x >= 0
    coinduction
    decreases delta(x)
  {
    x := x + 1;
  }
}
```

`while true` is the paper's `iterℓ(c); false`: its exit case is vacuous.

## VCGen: the temporal generator

A separate object (`verify/Temporal.scala`), called by `VCGen.verify` for temporal methods; the other methods
are unchanged. It shares `contract`, `Old.elim`, `decreases`, and the error reporting.

```
wp(progs, exit, jumps, ψ)    // progs: the rest of the body, exit/jumps: formulas, ψ: the current guarantee
```

- **State.** The flexible variables `vs` are the local variables in scope, the outputs, and the modified
  globals. Inputs, unmodified globals, the entry values of `Old.elim`, and all logical variables are rigid.
- **Steps (5)**, forward: after an assignment, the old state gets fresh names `vs₀` instead of renaming the
  rest of the program (equivalent to `κ'`, by renaming the bound `x'`):
  `∀vs₀. step(vs₀, vs) ⇒ wp(rest | unfold(ψ, vs₀, vs))`, where `step` is `x = e[vs := vs₀]` for the
  assigned variables and `y = y₀` for all others. `unfold` substitutes `vs ↦ vs₀` in the current-state part and
  keeps the shifted part over `vs`.
  - Steps: `Assign`, havoc (`Spec` with variables), and the tests of `If` and `While` (the paper's `assume`).
  - `assert`/`assume` (`Spec` without variables) are ghost, with no step:
    `P ∧ (P ⇒ wp(rest | ψ))` and `P ⇒ wp(rest | ψ)`.
- **Branches** `If`, `Choice`: one conjunct per branch, each followed by the whole rest. This is exponential
  in sequential branches, like symbolic execution, and `-split` separates the goals.
- **Loops (6)**, for `ι` and `H` from the clauses, `ω` fresh over `vs`:
  - entry `ι ⇒ ψ` (with the default `ι = inv ⇒ ψ`, this amounts to the invariant initially);
  - exit `∀mod. ¬b ⇒ wp(rest | ι)` (vacuous for `while true`);
  - step `∀mod. b ⇒ wp(body; ω(vs) | H(ω(vs)) ⇒ ι)`.
  - Jumps out of the body: `continue` is the continuation `ω(vs)`; `break` is `ι` itself, since the exit case
    proves `rest ⇒ ι` for all states and continuations are monotone (axiom 15); `return` is the exit of the
    method.
  - Every path through the body must take a step (a check). Otherwise the iteration of empty traces is
    outside the semantics, whose actions all take a step.
- **The exit of the method:** `ensures ∧ (ensures ⇒ collapse(ψ))`, where `collapse` evaluates `ψ` on the
  trace that repeats the final state forever (the stuttering completion of Section 2): `◦φ, □φ, ♢φ ↦ φ`,
  `φ U ψ ↦ ψ`, `φ W ψ ↦ φ ∨ ψ`, `φ R ψ ↦ ψ`, `φ W⁺ ψ, φ R⁺ ψ ↦ φ` (the fixpoints on a constant trace), with
  placeholders kept as atoms. This is exact and needs no annotation. The alternative, continuation `false`, would
  accept any terminating method, including one that violates `□P` before it ends.
- **Rejected in temporal methods (first version):** calls (a call by contract hides the intermediate
  states; a later version could take calls to methods with `guarantees` by their contract, or treat calls as
  atomic steps on request), `Ode`, `Par`, `send`/`receive`. `-teq` and `-chc` reject temporal methods.
- **Goal:** `∀ ins, vs, gs. wp(body, exit, ..., requires ⇒ guarantees)`, preceded by the declarations of the
  placeholders.

## Discharging the goals (second step)

The goals are temporal. The first version prints them (`-print dfy`), which is enough for tests. For the
solvers, a lowering in `-fallback`, which already lowers what the solvers cannot express and marks the results
`:abstract`:

1. Expand each remaining temporal subformula once at the current state (the `unfold` laws, with nothing
   shifted, so `□φ ↦ φ ∧ ◦□φ`), on both sides of the implication.
2. Replace each maximal remaining `Prop` (`next ...`, placeholders, and operators left inside other binders)
   by a fresh predicate over its free **rigid** variables, with
   one predicate per syntactically equal atom (modulo renaming of bound variables). This is sound once the
   top-level universals are skolemized, since all atoms are then evaluated on one trace.
3. The goal is `:abstract`, since a refutation is no counterexample (`pipe.Verify`).

By hand, Examples 3 and 4 close this way. In Example 3 the disjunct `odd(x'') ∧ ω(x'')` meets the premise
`ω(x'')`. In Example 4, `□(δ(x') < z ∧ ω(x') ∧ C(ω(x')) ⇒ ι')` expands to its instance now, and both of its
cases give `♢prime(x')`, whose expansion is the atom of the goal. In general, entailments like
`□(x = v) ∧ odd(v) ⇒ □odd(x)` need a real LTL-modulo-theories oracle (the paper's future work), so the
lowering is sound but incomplete.

## Points in the paper to check

These came up while mapping the rules onto the code. I may be misreading them, so they are worth a look in the
Isabelle formalization.

1. **Flexible quantifiers and `M`.** The semantics makes quantified variables flexible (a value per state),
   and `unfold` primes bound variables. Then `z` in `Mδ` is chosen per state: the hypothesis holds trivially by
   `zᵢ ≤ δᵢ` for `i > 0`, and after `unfold`, `z'` is unrelated to `z`, so Example 4's step
   `δ(x') < δ(x) = z` does not reach the hypothesis. The plan therefore makes logical variables **rigid**
   (`unfold(Q y. φ) = Q y. unfold(φ)`), and only program variables flexible.
2. **`x = mod(A)` in rule (5).** The premise of Lemma 4 / Axiom 1, `∀τ. τ' ⇔ ◦τ`, renames only `x`. For a
   `τ` over an unmodified `y` it then says `τ ⇔ ◦τ`, i.e., `y` constant forever, which a later assignment to
   `y` contradicts. The plan steps all flexible variables, with frame equations `y = y₀`.
3. **Zero-step commands.** Ghost `assert`/`assume`, and the exit by stuttering, are additions outside the
   mechanized rules. They are harmless as far as I can see, but they are not covered by the Isabelle proofs.
4. Small things: Example 3 writes `x'' = x + 4` for `x'' = x' + 4`. The proof of Theorem 1 cites (13) twice and
   "definition (5)" for rule (2). Lemma 2 needs `ι` in exactly the given shape, so the generator must
   normalize `inv ⇒ (♢φ ⇒ γ)` to it.

## Plan

1. **Core `Prop`** (done): the case and its places (Expr, Subst, Type, both Simplify, printers).
2. **Dafny syntax** (done): the mixfix tables, the scanner rules for `until+`/`unless+`/`release+` and `ω`,
   `Parser.resolve` of operators and placeholders, the printer with precedences and parentheses; the SMT-LIB
   parser and printer. Tests `examples/dafny/printing/temporal.dfy` (compared as text),
   `examples/dafny/parsing/temporal_*.dfy` (SMT-LIB output, `!always p`, non-`Bool` operands, placeholders on
   expressions), `examples/smtlib/parsing/temporal*.smt2` (functions of the same names, arity),
   `examples/dafny/prove/temporal*.dfy` (no facts inside the operators, in `-simplify` and `-prove`).
3. **Clauses**: `guarantees`, `coinduction`, `induction` in grammar, scanner, parser, `Attrs.guarantees`, Dafny
   printer, SMT-LIB parser; rejected by the other printers, `-teq`, and `-chc`.
4. **`Temporal` in `verify`**: `unfold`, `collapse`, the hypothesis operators, the rules above, the checks
   (calls, steps in loop bodies, the shapes for `C`/`I`). Tests `examples/dafny/ltl/` with the goals as
   `.out`: Examples 1/4 (`primes.dfy`), 3 (`odd.dfy`), branches, `break`/`continue`/`return` in loops, a
   terminating method against `always P` (violated before the exit), and `induction` from a
   `requires eventually ...`.
5. **The lowering** in `-fallback`. The tests become `-vcgen -fallback -z3`, with `// expected: valid` where
   the one-step expansion suffices.
6. **Docs**: `doc/ltl.md`, `datastructures.md` (`Prop`), `options.md`, `architecture.md` (VCGen, the Dafny
   operators), and the README. Then this file goes.

Steps 1–3 are one minor version, and steps 4–5 the next.

## Decisions for the user

- Rigid logical variables (point 1) and stepping all flexible variables (point 2), postponed.
- Steps: `if`/`while` tests as steps (paper) with ghost `assert`/`assume`, or tests without a step.
- The exit of a temporal method: stuttering (recommended), or `false` as in the examples of the paper.
- Clause keywords: `guarantees`, `coinduction`, `induction` (alternatives: `rely`/`guarantee`, which clash with
  rely-guarantee; a single clause `hypothesis C, M`).
- The lowering in `-fallback`, or a transform of its own.
