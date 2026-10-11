// naturals and arithmetic: the values of naturals as integers and back, small constants, and the lemmas of arithmetic
// in the normal form of the simplifier (division, remainders, powers) extracted from teq.dfy on Oct 11, 2026 as one of
// its modules, teq.dfy itself is unchanged; this file assumes the core declarations of teq.dfy (Nat, integer, natural,
// List, length, unspecified, Trace, current, butlast, counter, earlier, prefix, occurs, indexof, distincts, consts);
// the attributes and the order of the lemmas are those of teq.dfy; the assembly of the preludes from the modules is not
// implemented yet, and the modules are not tested

// powers, which are not unfolded
function {:teq} pow(c: int, n: Nat): int
{
  match n
  case zero => 1
  case succ(m) => c * pow(c, m)
}

lemma {:rw} {:teq} natural_integer(n: Nat)
  ensures natural(integer(n)) == n

lemma {:rw} {:teq} integer_natural(x: int)
  requires 0 <= x
  ensures integer(natural(x)) == x

lemma {:rw} {:teq} zero_integer(n: Nat)
  ensures (n == zero) <==> (integer(n) == 0)

// loops whose numbers of iterations have the same value, e.g. N for loops in sequence, iterate equally often
// (from ss1)
lemma {:rw} {:teq} integer_injective(m: Nat, n: Nat)
  ensures (integer(m) == integer(n)) <==> (m == n)

// small constants as naturals and back, e.g. the iterations of loops with literal bounds, and indices of reads
// the natural of a value that is not positive is zero, e.g. the iterations of a loop that does not run
lemma {:rw} {:teq} natural_nonpositive(x: int)
  requires x <= 0
  ensures natural(x) == zero

lemma {:rw} {:teq} natural_zero()
  ensures natural(0) == zero

lemma {:rw} {:teq} natural_one()
  ensures natural(1) == succ(zero)

lemma {:rw} {:teq} natural_two()
  ensures natural(2) == succ(succ(zero))

lemma {:rw} {:teq} integer_zero()
  ensures integer(zero) == 0

lemma {:rw} {:teq} integer_one()
  ensures integer(succ(zero)) == 1

lemma {:rw} {:teq} integer_two()
  ensures integer(succ(succ(zero))) == 2

// even summands do not change the remainder modulo 2
// (from array_monotonic, phases_1-1, phases_1-2)
lemma {:rw} {:teq} mod_add_even(x: int, n: int)
  ensures (x + 2 * n) % 2 == x % 2

// a positive number divides itself
// (from modn, modnf)
lemma {:rw} {:teq} mod_self(x: int)
  requires 0 < x
  ensures x % x == 0

// division of a multiple of m plus a remainder below m
// (from half)
lemma {:rw} {:teq} div_quotient_remainder(m: int, k: int, r: int)
  requires 0 < m && 0 <= r < m
  ensures (m * k + r) / m == k

// twice a number is the product of consecutive numbers iff it is its half, as an equivalence of atoms, since an
// equation of integers as a lemma rewrites its left-hand side as a term
// (from gauss_sum)
lemma {:rw} {:teq} double_eq_half(n: int, s: int)
  ensures (2 * s == n + n * n) <==> (s == (n + n * n) / 2)

// the sum 0 + 1 + ... + (n - 1) plus 1 is at least n
// (from afnp2014)
lemma {:rw} {:teq} triangle_bound(n: int)
  ensures n <= (-n + n * n) / 2 + 1

// division by 2 of polynomials with even coefficients, since a generic (2 * a + 2 * b) / 2 does not match literal
// coefficients
// (from eqn1, eqn1f)
lemma {:rw} {:teq} half_2x_2xx(x: int)
  ensures (2 * x + 2 * x * x) / 2 == x + x * x

// the same
// (from nsqm, nsqmf, sqm)
lemma {:rw} {:teq} half_4x_2xx(x: int)
  ensures (4 * x + 2 * x * x) / 2 == 2 * x + x * x

// the same
// (from pcomp, pcompf)
lemma {:rw} {:teq} half_6x_6xx(x: int)
  ensures (6 * x + 6 * x * x) / 2 == 3 * x + 3 * x * x

// the same
// (from eqn2)
lemma {:rw} {:teq} half_4x_4xx(x: int)
  ensures (4 * x + 4 * x * x) / 2 == 2 * x + 2 * x * x

// literal factors cancel in a division by them
// (from array_of_struct_ptr_monotonic, sum_by_3)
lemma {:rw} {:teq} half_2x(x: int)
  ensures (2 * x) / 2 == x

lemma {:rw} {:teq} third_3x(x: int)
  ensures (3 * x) / 3 == x

// the sums 0 + 1 + ... + x and 0 + 1 + ... + (x - 1) are nonnegative for all integers x, x * (x + 1) and x * (x - 1)
// being products of consecutive numbers, also plus a nonnegative d
// (from array_init_var_plus_ind, -ind2, -ind3, benchmark20_conjunctive)
lemma {:rw} {:teq} triangle_nonneg(x: int)
  ensures 0 <= (x + x * x) / 2

lemma {:rw} {:teq} triangle_nonneg_below(x: int)
  ensures 0 <= (-x + x * x) / 2

lemma {:rw} {:teq} triangle_nonneg_add(x: int, d: int)
  requires 0 <= d
  ensures 0 <= (x + x * x) / 2 + d

lemma {:rw} {:teq} triangle_nonneg_below_add(x: int, d: int)
  requires 0 <= d
  ensures 0 <= (-x + x * x) / 2 + d

// a quotient below b + 1: x / d is at most b for 0 <= x < d * (b + 1)
// (from mlceu2)
lemma {:rw} {:teq} div_below(b: int, x: int, d: int)
  requires 0 < d && 0 <= x && x < d * (b + 1)
  ensures (b < x / d) <==> false

// the quotient of a positive divisor is not positive exactly below it
// (from MonoCera: pr2)
lemma {:rw} {:teq} div_nonpos(x: int, c: int)
  requires 0 < c
  ensures (x / c <= 0) == (x < c)

// a power of 2 is not divisible by 3
// (from underapprox_1-1, underapprox_1-2)
lemma {:rw} {:teq} pow_two_mod_three(n: Nat)
  ensures (pow(2, n) % 3 == 0) <==> false

// a nonnegative factor cancels in a strict comparison; does not match a literal coefficient (see TODO.md)
// (from count_by_k)
lemma {:rw} {:teq} mul_lt_cancel(k: int, a: int, b: int)
  requires 0 <= k
  ensures (k * a < k * b) <==> (0 < k && a < b)
