// series: the closed forms of the sums of the powers of a counter (Faulhaber's formulas) and of geometric sequences and
// series, for the polynomial loops of SV-COMP (nla-digbench: the power sums ps2 to ps6, geo; array-fpi: ncomp, pcomp);
// an optional module over teq.dfy, teq:aggregation (sum) and teq:arithmetic (pow), included after them
// (-include teq:series), collected on Oct 23, 2026; the forward facts are triggered at folds (squares, cubes, fourths,
// fifths, series), not at general terms such as a sum over a counter or the current value of a trace, whose triggers,
// tried at every such term, slow down the tasks they do not apply to (zero_sum4: 857 rewrites of integer(n) instead of
// 193, until the bound on the steps is exhausted)

// the sums of the powers of a counter by 1 from i, abstracted by folds (see above); the offset i in each fold, not a
// rule that shifts counters to 0, which would change the normal form of every map over a counter, e.g. of the reads of
// arrays
// (from nla-digbench: ps3 to ps6; MonoCera: ncomp, pcomp)
function {:teq} {:fold} squares(i: int, n: Nat): int
{
  sum(maps(for ⌊counter(i, 1, n)⌋ yield k :: k * k))
}

function {:teq} {:fold} cubes(i: int, n: Nat): int
{
  sum(maps(for ⌊counter(i, 1, n)⌋ yield k :: k * k * k))
}

function {:teq} {:fold} fourths(i: int, n: Nat): int
{
  sum(maps(for ⌊counter(i, 1, n)⌋ yield k :: k * k * k * k))
}

function {:teq} {:fold} fifths(i: int, n: Nat): int
{
  sum(maps(for ⌊counter(i, 1, n)⌋ yield k :: k * k * k * k * k))
}

// the sums over no iterations, e.g. in the case n == zero of a split, whose instances of the closed forms below would
// be polynomials in integer(zero), simplified again at every fact (ps5-ll_unwindbound1: the rewrite steps exhausted)
lemma {:rw} {:teq} squares_zero(i: int)
  ensures squares(i, zero) == 0

lemma {:rw} {:teq} cubes_zero(i: int)
  ensures cubes(i, zero) == 0

lemma {:rw} {:teq} fourths_zero(i: int)
  ensures fourths(i, zero) == 0

lemma {:rw} {:teq} fifths_zero(i: int)
  ensures fifths(i, zero) == 0

// a coefficient of the powers, as the expansions of (k + 1)^p leave them, e.g. 3 * k * k of ps4, outside the folds:
// a * squares(i, n) is linear in the fold, and a fold with a coefficient would not match the powers without one (the
// pattern a * k * k does not match k * k, whose normal form has no factor 1); sum_scale of teq:aggregation does not
// take the coefficient out of the mapped function
lemma {:rw} {:teq} sum_squares_scaled(a: int, i: int, n: Nat)
  ensures sum(maps(for ⌊counter(i, 1, n)⌋ yield k :: a * k * k)) == a * squares(i, n)

lemma {:rw} {:teq} sum_cubes_scaled(a: int, i: int, n: Nat)
  ensures sum(maps(for ⌊counter(i, 1, n)⌋ yield k :: a * k * k * k)) == a * cubes(i, n)

lemma {:rw} {:teq} sum_fourths_scaled(a: int, i: int, n: Nat)
  ensures sum(maps(for ⌊counter(i, 1, n)⌋ yield k :: a * k * k * k * k)) == a * fourths(i, n)

// the sums of the powers from i, Faulhaber's formulas (Academia Algebrae, 1631) times their denominators, as the
// difference of the sums below i + integer(n) and below i, without division: forward facts about the folds, which stay
// atoms of the linear arithmetic (as rewrite rules with a quotient, the quotient needs an exactness fact whose trigger
// a forward lemma cannot name, all its terms having one variable); triggered at the fold, the term with the most
// variables, once per fold; in integer(n), which the arithmetic relates to the variables equal to it, e.g. the final
// value c of a loop counter, since it inlines the solution c == integer(n) (0.50.16; before, the facts were stated in
// such a c, looked up among the facts, which matched every variable of the class of integer(n), with an instance each,
// until the rewrite steps were exhausted on ps5-ll_unwindbound1)
// (from nla-digbench: ps3 to ps6; MonoCera: ncomp, pcomp)
lemma {:fw} {:teq} squares_closed(i: int, n: Nat)
  ensures 6 * squares(i, n)
    == (i + integer(n) - 1) * (i + integer(n)) * (2 * (i + integer(n)) - 1)
       - (i - 1) * i * (2 * i - 1)

lemma {:fw} {:teq} cubes_closed(i: int, n: Nat)
  ensures 4 * cubes(i, n)
    == (i + integer(n)) * (i + integer(n)) * (i + integer(n) - 1) * (i + integer(n) - 1)
       - i * i * (i - 1) * (i - 1)

lemma {:fw} {:teq} fourths_closed(i: int, n: Nat)
  ensures 30 * fourths(i, n)
    == (i + integer(n)) * (i + integer(n) - 1) * (2 * (i + integer(n)) - 1)
         * (3 * (i + integer(n)) * (i + integer(n)) - 3 * (i + integer(n)) - 1)
       - i * (i - 1) * (2 * i - 1) * (3 * i * i - 3 * i - 1)

lemma {:fw} {:teq} fifths_closed(i: int, n: Nat)
  ensures 12 * fifths(i, n)
    == (i + integer(n)) * (i + integer(n)) * (i + integer(n) - 1) * (i + integer(n) - 1)
         * (2 * (i + integer(n)) * (i + integer(n)) - 2 * (i + integer(n)) - 1)
       - i * i * (i - 1) * (i - 1) * (2 * i * i - 2 * i - 1)

// geometric sequences: a value multiplied by z in each iteration is its initial value times a power of z, the function
// pow of teq:arithmetic, which is not unfolded but an atom of the arithmetic
// (from nla-digbench: geo1, geo2, geo3)
lemma {:rw} {:teq} current_trace_geometric(y0: int, z: int, n: Nat)
  ensures current(trace(y0, for ⌊counter(0, 1, n)⌋ do y, k :: y * z)) == y0 * pow(z, n)

// a geometric series, multiplied by z and added a in each iteration, abstracted by a fold (see above): at the current
// value of any trace with such an update, the trigger slows down tasks with many traces (zero_sum4 from 30 s to 43 s,
// without a single instance)
// (from nla-digbench: geo1, geo2, geo3)
function {:teq} {:fold} series(x0: int, z: int, a: int, n: Nat): Trace<int>
{
  trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: x * z + a)
}

// without division: (z - 1) times its value plus a is the same power of z times (z - 1) times its initial value plus
// a; a forward fact, since the value is a quotient by z - 1, which is 0 for z == 1
lemma {:fw} {:teq} current_series(x0: int, z: int, a: int, n: Nat)
  ensures (z - 1) * current(series(x0, z, a, n)) + a == ((z - 1) * x0 + a) * pow(z, n)
