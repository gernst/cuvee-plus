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

// the sums of the powers from i, Faulhaber's formulas times their denominators, as the difference of the sums below
// i + c and below i, without division, as forward facts about the folds, which stay atoms of the linear arithmetic (as
// rewrite rules with a quotient, the quotient needs an exactness fact whose trigger a forward lemma cannot name, all its
// terms having one variable); in a variable c equal to the number of iterations, e.g. the final value of a loop
// counter, looked up among the facts: the linear arithmetic does not relate the powers of c to those of integer(n)
// (c * c and integer(n) * integer(n) are different monomials), hence the powers of integer(n) that remain, e.g. of
// the sums of a counter (sum_counter), are related to those of c by the lemmas below, each one equation triggered at
// a fold or at a quotient: a link at integer(n) as its trigger slows down every task with a counter (array_4 from 19 s
// to a timeout of 90 s) or exhausts the rewrite steps (in-de61.1 of SV-LIB, whose five loops have counters equal to
// each other), and the higher powers of integer(n) linked to c do not terminate on mono-crafted_13
// (from nla-digbench: ps3 to ps6; MonoCera: ncomp, pcomp)
lemma {:fw} {:teq} squares_at(c: int, i: int, n: Nat)
  requires c == integer(n)
  ensures 6 * squares(i, n) == (i + c - 1) * (i + c) * (2 * (i + c) - 1) - (i - 1) * i * (2 * i - 1)

// the halved triangles in integer(n) that sum_counter of teq:aggregation leaves for the sum of a counter, e.g.
// (-integer(n) + integer(n) * integer(n)) / 2 of the sum of y = k + 1 of ps2, in c as well, at the quotient as its
// trigger, which occurs only where such a sum was rewritten: one equation each, since the engine splits a forward
// lemma at its conjunctions and triggers each conjunct on its own, and the conjuncts integer(n) * integer(n) == c * c
// of a former squares_at were triggered at integer(n), at every counter (in-de61.1 of SV-LIB: rewriting does not
// terminate); the coefficient a separately, since a * x does not match x
// (from nla-digbench: ps2 to ps6; MonoCera: ncomp, pcomp)
lemma {:fw} {:teq} triangle_at(c: int, n: Nat)
  requires c == integer(n)
  ensures 2 * ((integer(n) + integer(n) * integer(n)) / 2) == c + c * c

lemma {:fw} {:teq} triangle_below_at(c: int, n: Nat)
  requires c == integer(n)
  ensures 2 * ((-integer(n) + integer(n) * integer(n)) / 2) == -c + c * c

lemma {:fw} {:teq} triangle_scaled_at(a: int, c: int, n: Nat)
  requires c == integer(n)
  ensures 2 * ((a * integer(n) + a * integer(n) * integer(n)) / 2) == a * c + a * c * c

lemma {:fw} {:teq} triangle_below_scaled_at(a: int, c: int, n: Nat)
  requires c == integer(n)
  ensures 2 * ((-a * integer(n) + a * integer(n) * integer(n)) / 2) == -a * c + a * c * c

// the square and the cube of integer(n) equated with those of c, e.g. the n * n of the sum of 2 * k + 1 of ps3, which
// no quotient holds: each as one equation with the fold, such that it is triggered at the fold (with squares_at, the
// linear arithmetic derives integer(n) * integer(n) == c * c), not at integer(n) as a conjunct of its own would be
// (from nla-digbench: ps3, ps5)
lemma {:fw} {:teq} squares_square_at(c: int, i: int, n: Nat)
  requires c == integer(n)
  ensures 6 * squares(i, n) + integer(n) * integer(n) == (i + c - 1) * (i + c) * (2 * (i + c) - 1) - (i - 1) * i * (2 * i - 1) + c * c

lemma {:fw} {:teq} squares_cube_at(c: int, i: int, n: Nat)
  requires c == integer(n)
  ensures 6 * squares(i, n) + integer(n) * integer(n) * integer(n) == (i + c - 1) * (i + c) * (2 * (i + c) - 1) - (i - 1) * i * (2 * i - 1) + c * c * c

lemma {:fw} {:teq} cubes_at(c: int, i: int, n: Nat)
  requires c == integer(n)
  ensures 4 * cubes(i, n) == (i + c) * (i + c) * (i + c - 1) * (i + c - 1) - i * i * (i - 1) * (i - 1)

lemma {:fw} {:teq} fourths_at(c: int, i: int, n: Nat)
  requires c == integer(n)
  ensures 30 * fourths(i, n)
    == (i + c) * (i + c - 1) * (2 * (i + c) - 1) * (3 * (i + c) * (i + c) - 3 * (i + c) - 1)
       - i * (i - 1) * (2 * i - 1) * (3 * i * i - 3 * i - 1)

lemma {:fw} {:teq} fifths_at(c: int, i: int, n: Nat)
  requires c == integer(n)
  ensures 12 * fifths(i, n)
    == (i + c) * (i + c) * (i + c - 1) * (i + c - 1) * (2 * (i + c) * (i + c) - 2 * (i + c) - 1)
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
