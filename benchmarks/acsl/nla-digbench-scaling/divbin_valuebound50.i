// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/divbin; the invariants are those of divbin2; b is B times a power of 2 by the predicate pow2mul of the axiomatic Pow2Mul (goal-directed axioms; 1 << k is uninterpreted)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

/*@ requires \false;
    assigns \nothing; */
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "divbin.c", 10, __extension__ __PRETTY_FUNCTION__); })); }
/*@ assigns \nothing; */
extern unsigned __VERIFIER_nondet_uint(void);
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR:
        {reach_error();}
    }
    return;
}
/*@ axiomatic Pow2Mul {
  predicate pow2mul(integer b, integer B);
  axiom pow2mul_base: \forall integer B; B >= 1 ==> pow2mul(B, B);
  axiom pow2mul_double: \forall integer b, integer B, integer d; pow2mul(b, B) && d == 2*b ==> pow2mul(d, B);
  axiom pow2mul_ge: \forall integer b, integer B; pow2mul(b, B) ==> b >= B;
  axiom pow2mul_even: \forall integer b, integer B; pow2mul(b, B) && b != B ==> b % 2 == 0;
  axiom pow2mul_half: \forall integer b, integer B, integer h; pow2mul(b, B) && b != B && b == 2*h ==> pow2mul(h, B);
} */
int main() {
  unsigned A, B;
  unsigned q, r, b;
    A = __VERIFIER_nondet_uint();
    assume_abort_if_not(A>=0 && A<=50);
    B = __VERIFIER_nondet_uint();
    assume_abort_if_not(B>=0 && B<=50);
    assume_abort_if_not(B < (0x7fffffff * 2U + 1U)/2);
    assume_abort_if_not(B >= 1);
    q = 0;
    r = A;
    b = B;
    /*@ loop invariant q == 0 && r == A;
        loop invariant b >= B;
        loop invariant pow2mul(b, B);
        loop assigns b; */
    while (1) {
        if (!(r >= b)) break;
        b = 2 * b;
    }
    /*@ loop invariant A == q*b + r;
        loop invariant r < b;
        loop invariant b >= B;
        loop invariant pow2mul(b, B);
        loop assigns q, r, b; */
    while (1) {
        __VERIFIER_assert(A == q * b + r);
        if (!(b != B)) break;
        q = 2 * q;
        b = b / 2;
        if (r >= b) {
            q = q + 1;
            r = r - b;
        }
    }
    __VERIFIER_assert(A == q * b + r);
    return 0;
}
