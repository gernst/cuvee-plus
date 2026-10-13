// arithmetic: the rules of integer arithmetic that the arithmetic of -prove does not decide on its own (division and
// remainders of non-literal arguments, products, powers); an optional module over teq.dfy alone (-include
// teq:arithmetic), migrated on Oct 13, 2026 from the module of the per-variable form (in legacy/teq.dfy): the rules on
// naturals and integers are in teq.dfy; left out are the rules that -prove decides without them (mod_add_even, the
// halves and thirds of polynomials with literal coefficients, natural_zero, integer_zero), those never applied on
// SV-COMP (natural_one, natural_two, integer_one, integer_two, and div_quotient_remainder, which does not match the
// product k * m of the normal form of -prove), and the sums with a nonnegative d of the triangle
// bounds, which follow from these as forward facts by the linear arithmetic; the bounds of the triangles are forward
// facts about their term, the others rewrite rules; the function pow of the former core.dfy is declared here

// powers, which are not unfolded
function {:teq} pow(c: int, n: Nat): int
{
  match n
  case zero => 1
  case succ(m) => c * pow(c, m)
}

// a positive number divides itself
// (from modn, modnf)
lemma {:rw} {:teq} mod_self(x: int)
  requires 0 < x
  ensures x % x == 0

// twice a number is the product of consecutive numbers iff it is its half, as an equivalence of atoms, since an
// equation of integers as a lemma rewrites its left-hand side as a term
// (from gauss_sum)
lemma {:rw} {:teq} double_eq_half(n: int, s: int)
  ensures (2 * s == n + n * n) <==> (s == (n + n * n) / 2)

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

// a nonnegative factor cancels in a strict comparison; does not match a literal coefficient (see TODO.md)
// (from count_by_k)
lemma {:rw} {:teq} mul_lt_cancel(k: int, a: int, b: int)
  requires 0 <= k
  ensures (k * a < k * b) <==> (0 < k && a < b)


// a power of 2 is not divisible by 3
// (from underapprox_1-1, underapprox_1-2)
lemma {:rw} {:teq} pow_two_mod_three(n: Nat)
  ensures (pow(2, n) % 3 == 0) <==> false

// the sum 0 + 1 + ... + (n - 1) plus 1 is at least n
// (from afnp2014)
lemma {:fw} {:teq} triangle_bound(n: int)
  ensures n <= (-n + n * n) / 2 + 1

// the sums 0 + 1 + ... + x and 0 + 1 + ... + (x - 1) are nonnegative for all integers x, x * (x + 1) and x * (x - 1)
// being products of consecutive numbers; plus a nonnegative d, the bound follows by the linear arithmetic
// (from array_init_var_plus_ind, -ind2, -ind3, benchmark20_conjunctive)
lemma {:fw} {:teq} triangle_nonneg(x: int)
  ensures 0 <= (x + x * x) / 2

lemma {:fw} {:teq} triangle_nonneg_below(x: int)
  ensures 0 <= (-x + x * x) / 2

// the triangles are exact, x * (x + 1) and x * (x - 1) being even, which the linear arithmetic needs where they are
// halved and doubled again, e.g. 2 * s == n * (n + 1) for the sum s of 1, ..., n
// (from gauss_sum)
lemma {:fw} {:teq} triangle_even(x: int)
  ensures 2 * ((x + x * x) / 2) == x + x * x

lemma {:fw} {:teq} triangle_even_below(x: int)
  ensures 2 * ((-x + x * x) / 2) == -x + x * x
