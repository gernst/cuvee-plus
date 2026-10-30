// series: the closed forms of the sums of the powers of a counter (Faulhaber's formulas) and of geometric sequences and
// series, for the polynomial loops of SV-COMP (nla-digbench: the power sums ps2 to ps6, geo; array-fpi: ncomp, pcomp);
// an optional module over teq.dfy, teq:aggregation (sum) and teq:arithmetic (pow), included after them
// (-include teq:series); the forward facts are triggered at folds (squares, cubes, fourths, fifths, series), not at
// general terms such as a sum over a counter or the current value of a trace, which would be tried at every such term

// the sums of the powers of a counter by 1 from i, abstracted by folds (see above); the offset i in each fold, not a
// rule that shifts counters to 0, which would change the normal form of every map over a counter, e.g. of the reads of
// arrays
// a coefficient, e.g. 3 * k * k of the expansion of (k + 1)^2, is taken out of the sum by sum_scale of teq:aggregation,
// which matches the product modulo associativity, commutativity and the factor 1
// (from nla-digbench: ps3 to ps6; MonoCera: ncomp, pcomp)
function {:teq} {:fold} squares(i: int, n: int): int
{
  sum(elems(maps(for ⌊counter(i, 1, n)⌋ yield k :: k * k)))
}

function {:teq} {:fold} cubes(i: int, n: int): int
{
  sum(elems(maps(for ⌊counter(i, 1, n)⌋ yield k :: k * k * k)))
}

function {:teq} {:fold} fourths(i: int, n: int): int
{
  sum(elems(maps(for ⌊counter(i, 1, n)⌋ yield k :: k * k * k * k)))
}

function {:teq} {:fold} fifths(i: int, n: int): int
{
  sum(elems(maps(for ⌊counter(i, 1, n)⌋ yield k :: k * k * k * k * k)))
}

// the sums over no iterations, e.g. in the case n <= 0 of a split, whose instances of the closed forms below would be
// polynomials in a count of 0, simplified again at every fact (ps5-ll_unwindbound1: the rewrite steps exhausted)
lemma {:rw} {:teq} squares_zero(i: int, n: int)
  requires n <= 0
  ensures squares(i, n) == 0

lemma {:rw} {:teq} cubes_zero(i: int, n: int)
  requires n <= 0
  ensures cubes(i, n) == 0

lemma {:rw} {:teq} fourths_zero(i: int, n: int)
  requires n <= 0
  ensures fourths(i, n) == 0

lemma {:rw} {:teq} fifths_zero(i: int, n: int)
  requires n <= 0
  ensures fifths(i, n) == 0

// the sums of the powers from i, Faulhaber's formulas (Academia Algebrae, 1631) times their denominators, as the
// difference of the sums below i + n and below i, without division: forward facts about the folds, which stay atoms of
// the linear arithmetic (as rewrite rules with a quotient, the quotient needs an exactness fact whose trigger a forward
// lemma cannot name, all its terms having one variable); triggered at the fold, the term with the most variables, once
// per fold; stated in n, not in a variable looked up by a condition, which would be matched against every member of
// its class
// (from nla-digbench: ps3 to ps6; MonoCera: ncomp, pcomp)
lemma {:fw} {:teq} squares_closed(i: int, n: int)
  requires 0 <= n
  ensures 6 * squares(i, n)
    == (i + n - 1) * (i + n) * (2 * (i + n) - 1)
       - (i - 1) * i * (2 * i - 1)

lemma {:fw} {:teq} cubes_closed(i: int, n: int)
  requires 0 <= n
  ensures 4 * cubes(i, n)
    == (i + n) * (i + n) * (i + n - 1) * (i + n - 1)
       - i * i * (i - 1) * (i - 1)

lemma {:fw} {:teq} fourths_closed(i: int, n: int)
  requires 0 <= n
  ensures 30 * fourths(i, n)
    == (i + n) * (i + n - 1) * (2 * (i + n) - 1)
         * (3 * (i + n) * (i + n) - 3 * (i + n) - 1)
       - i * (i - 1) * (2 * i - 1) * (3 * i * i - 3 * i - 1)

lemma {:fw} {:teq} fifths_closed(i: int, n: int)
  requires 0 <= n
  ensures 12 * fifths(i, n)
    == (i + n) * (i + n) * (i + n - 1) * (i + n - 1)
         * (2 * (i + n) * (i + n) - 2 * (i + n) - 1)
       - i * i * (i - 1) * (i - 1) * (2 * i * i - 2 * i - 1)

// geometric sequences: a value multiplied by z in each iteration is its initial value times a power of z, the function
// pow of teq:arithmetic, which is not unfolded but an atom of the arithmetic
// (from nla-digbench: geo1, geo2, geo3)
lemma {:rw} {:teq} current_trace_geometric(y0: int, z: int, n: int)
  ensures current(trace(y0, for ⌊counter(0, 1, n)⌋ do y, k :: y * z)) == y0 * pow(z, n)

// a geometric series, multiplied by z and added a in each iteration, abstracted by a fold (see above): at the current
// value of any trace with such an update, the trigger slows down tasks with many traces (zero_sum4 from 30 s to 43 s,
// without a single instance)
// (from nla-digbench: geo1, geo2, geo3)
function {:teq} {:fold} series(x0: int, z: int, a: int, n: int): Trace<int>
{
  trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: x * z + a)
}

lemma {:rw} {:teq} length_series(x0: int, z: int, a: int, n: int)
  requires 0 <= n
  ensures length(⌊series(x0, z, a, n)⌋) == n

// no iteration: the initial value, which current_series below does not give for z == 1
lemma {:rw} {:teq} current_series_none(x0: int, z: int, a: int, n: int)
  requires n <= 0
  ensures current(series(x0, z, a, n)) == x0

// without division: (z - 1) times its value plus a is the same power of z times (z - 1) times its initial value plus
// a; a forward fact, since the value is a quotient by z - 1, which is 0 for z == 1
lemma {:fw} {:teq} current_series(x0: int, z: int, a: int, n: int)
  ensures (z - 1) * current(series(x0, z, a, n)) + a == ((z - 1) * x0 + a) * pow(z, n)
