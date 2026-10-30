# Nonlinear loops (nla-digbench)

Analysis of Oct 29, 2026: the open tasks of nla-digbench and nla-digbench-scaling with the verdict true in the cloud run
of 0.53.14 without fallback (`-svcomp -rules`), 221 tasks of 24 programs (20 of nla-digbench, the rest the
`_unwindbound`/`_valuebound` variants of the same programs). 46 ended in `unknown` with a residual goal in the log
(cohencu, cohendiv, geo2, geo3, mannadiv, freire1, one bresenham); the other 175 timed out, whose logs are empty, so
their loops are read from the sources (and the trace systems of `-teq` without `-prove`). No lemma is tried yet.

Two kinds of gaps: traces that no lemma folds or reads (part A), and the arithmetic that remains once they are (part B).
Most of A is one principle, the invariant that every case of an update preserves (A1).

## A. Traces that are not folded or read

### A1. Quantities that every case preserves (most of the family)

The asserted equations of dijkstra, knuth, egcd, egcd2, egcd3, lcm1, lcm2, fermat1, fermat2, divbin, divbin2, hard,
prod4br, prodbin, bresenham, cohendiv are polynomial invariants of the loop: each case of the update keeps them, e.g.
egcd (`a > b ? (a -= b, p -= q, r -= s) : (b -= a, q -= p, s -= r)`) keeps `a == p*x + r*y` and `b == q*x + s*y`,
fermat2 keeps `4*(A + r) == u*u - v*v - 2*u + 2*v`, prod4br keeps `q + a*b*p == x*y`. These loops have no closed
form (a guard compares accumulators, the subtractive Euclid), so the folds of the database do not apply, and a closed
form is not what the goal needs.

The principle is induction as a rule on the goal: an atom `P(current(S))` over the trace `S` of a component holds if
`P` holds of the initial values and every case of the update preserves it,
`invs(for deps check x, ... :: P(x) ==> P(update(x)))`. `P` is the atom itself, abstracted at the current value (a
higher-order instance that contains the term it abstracts, as `Rewrite.abstraction` requires); several equations that
only hold together (egcd's two) need their conjunction as `P`, which is the goal of the asserting loop body. The side
condition is a polynomial identity per case, decided by the normalization of polynomials if it is linear in the
products that occur, otherwise part B.

Open questions: whether one such rule is acceptable in the database (it is the general rule of loops, which the
trace equations otherwise replace by closed forms); which `P` to take when the goal is not a single atom over one
trace; the components of several accumulators (`Component(S, i)`), since these loops are cycles of several variables.

### A2. Wrap-around modulo 2^64 of affine updates (geo1-ll, geo2-ll, geo3-ll, 33 tasks)

Done (Oct 29-30): `current_trace_mod_affine` and `current_trace_mod_mul` (unsigned.dfy, after the additions
`current_trace_mod_add_*`, which lift the remainder already; one lemma per form, since a higher-order summand is not
matched as 0). Cloud run of Oct 30: geo2-ll, geo2-ll_valuebound20/50/100, geo3-ll_valuebound20/50/100 correct. Open
were geo3-ll and the unwindbound variants, whose loops run at most a literal number of times: their residual goals had
`pow(z, 0)`, `pow(z, 1)` and `current(series(1, z, 1, 1))`, which only the forward fact of series related. Since Oct 30
the value of a series for no and one iteration is a polynomial (`current_series_zero`, `current_series_one`, with
`pow_zero`, `pow_one`); for a symbolic count it stays the forward fact at the value. A closed form over a named
geometric sum, `x0 * pow(z, n) + a * geometric(z, n)` (0.53.19), lost geo1-3_valuebound5 and _valuebound10 on the
cloud: the arithmetic does not multiply the definition of the value out, so the product of the value with z in the
goal was no monomial of the forward fact about the sum (option B, substituting such definitions into products, is an
engine change, not taken). geo1-ll
ends in "rewriting does not terminate" (bugs.md).

`x = (x*z + 1) % 2^64`, `y = (y*z) % 2^64` (unsigned long long) stay raw traces: `current_trace_geometric` and the fold
`series` match `y * z` and `x * z + a`, not their remainders. Residual goal of geo2-ll:

```
(= (mod (+ (* 18446744073709551615 x$18) (* x$18 z$6) (* 18446744073709551615 y$19 z$6) 1) 18446744073709551616) 0)
```

Principle: reduction modulo M commutes with the operations of the ring, so the final value of a trace whose update is
an affine map taken modulo M is the final value of the trace without it, modulo M:
`current(trace(x0, ... :: (x * A + B) % M)) == current(trace(x0, ... :: x * A + B)) % M` for `0 <= x0 < M` (the
case of no iteration). Then `series` and `current_trace_geometric` apply, and the goal holds modulo M because it holds
over the integers (`current_series` gives `(z - 1) * x + 1 == z * pow(z, n)`).

### A3. A trace that does not read its accumulator (cohendiv-ll, 15 tasks)

Done (Oct 29): `current_trace_last` (counters.dfy); cohendiv-ll correct locally in 62 s.

The outer loop of cohendiv keeps `a` and `b` of the inner loop: `trace(0, ... :: pow(2, n))`, the update is the last
value, not an accumulation. Its current value is the update at the last iteration (or the initial value for none):
`current(trace(x0, for ks, hs do x, k, h :: F(k, h)))` is `F` at the last elements. `current_trace_constant` is the
case of a constant `F`. With it, cohendiv's residual goal `b == a * y` is `pow(2, m) * y == pow(2, m) * y`.

### A4. Doubling with a literal factor (cohendiv, hard, divbin, divbin2, prodbin, dijkstra)

The inner loop of cohendiv, `a = 2 * a` (`trace(1, ... :: (* 2 v0))`), stays raw: `current_trace_geometric` has the
pattern `y * z`, and the product with the literal first does not bind the accumulator. To check whether a variant
`z * y` matches, or the matcher of products. Then the doubling loops are `pow(2, n)` and the halving loops
(`b = b / 2`, `q = q / 4`) their inverse, which needs part B.

### A5. Increments chosen by a guard on the accumulator (bresenham, fermat2, mannadiv)

bresenham: `v < 0 ? v += 2Y : (v += 2Y - 2X, y++)`; the guard reads `v`, so `sums` does not fold `v` (a guard that
reads the accumulator excludes the map), while `y` counts the second case over the history of `v` (`counts`). The
principle: a value with a constant increment per case is its initial value plus the increments counted by case,
`v == v0 + 2Y n - 2X y`, where both count the same guard over the same history. mannadiv's reset counter
(`y + 1 == c ? 0 : y + 1`) is the counter modulo `c` (`mods` of teq:unsigned), if the initial value is below `c`.

### A6. Binary expansion (prodbin, prod4br, divbin, divbin2, hard, dijkstra)

`y = y / 2` by the parity of `y` (`quot(y - 1, 2)` and `quot(y, 2)` in the two cases, equal for odd `y`), `z += x`
for odd `y`: `z` is `a` times the bits of `b` seen so far. Closed forms exist (`b / pow(2, k)`,
`sum of pow(2, k) * ((b / pow(2, k)) % 2) == b % pow(2, n)`), but they need division by powers in the arithmetic; A1
is the simpler route for these (the asserted invariant `z + x*y == a*b` is preserved by both cases).

### A7. Trace systems that explode (egcd2-ll, egcd3-ll, fermat1-ll, lcm1)

Nested loops whose `-teq` output has 3120 to 23664 traces (egcd2 3120, fermat1 3248, egcd3 21352, lcm1 23664, against
3-48 for the others): they time out before any lemma matters. A question of `TEQ.system` for nested loops of several
accumulators, not of the database.

## B. Nonlinear arithmetic after folding

- **Exact division in polynomials** (cohencu-ll, 7 tasks): the closed form `x == (3a + 3a²) / 2 + 3 * squares(0, n) + a
  + 1` with `n == a + 1`; the goal `10a + 12a² + 6a³ + a⁴ + 3 == (a + 3) * x` is a polynomial identity once the
  quotients by 2 are known to be exact (`triangle_even`) and `squares` is its Faulhaber form, but `(a + 3) * x` is a
  product of a variable and an atom with a quotient, which the linear simplex does not multiply out. Principle: a
  quotient by a literal that is exact in the context as a rational coefficient of the polynomial (the polynomials have
  rational coefficients already, `Arith.Poly`).
- **Division by a symbolic divisor** (mannadiv): `x2 * (n / x2) + n % x2 == n`, the definition of division for a
  divisor that is no literal; the simplex knows it for literals only.
- **Products of atoms from closed forms** (geo1-3 after A2, cohendiv after A3): linear in the atoms `pow(z, n)` and
  `z * pow(z, n)` once the forward facts are there; to check after A2.
- **Floating point** (freire1, 7 tasks): `Double_sub`, `Double_of_int` of the uninterpreted sorts of floats; out of
  scope.

## Order, by tasks per concept

1. A2 (33 tasks: geo1-3 with variants), local and principled; then check the arithmetic of B on them.
2. A3 and A4 (cohendiv, 15 tasks), small lemmas.
3. A1, the general rule; most of the remaining 150 tasks, but a design decision first (open questions above).
4. B, exact division (cohencu, 7 tasks), an engine change of the polynomials.
5. A7, the size of the trace systems of nested loops (4 programs, about 40 tasks), in TEQ.
