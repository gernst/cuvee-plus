// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/divbin2; b is a power of 2 (B is 1) by the predicate pow2 of the axiomatic Pow2 (goal-directed axioms; 1 << k is uninterpreted); the ranges of the unsigned variables that the loops assign are loop invariants
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "divbin2.c", 10, __extension__ __PRETTY_FUNCTION__); })); }
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
/*@ axiomatic Pow2 {
  predicate pow2(integer p);
  axiom pow2_one: pow2(1);
  axiom pow2_double: \forall integer p, d; pow2(p) && d == 2*p ==> pow2(d);
  axiom pow2_pos: \forall integer p; pow2(p) ==> p >= 1;
  axiom pow2_even: \forall integer p; pow2(p) && p != 1 ==> p % 2 == 0;
  axiom pow2_half: \forall integer p, h; pow2(p) && p != 1 && p == 2*h ==> pow2(h);
} */
int main() {
  unsigned A, B;
  unsigned q, r, b;
    A = __VERIFIER_nondet_uint();
    assume_abort_if_not(A>=0 && A<=20);
    B = 1;
    q = 0;
    r = A;
    b = B;
    /*@ loop invariant q == 0 && r == A;
        loop invariant b >= B;
        loop invariant pow2(b);
        loop invariant 0 <= b <= 4294967295;
        loop assigns b; */
    while (1) {
        if (!(r >= b)) break;
        b = 2 * b;
    }
    /*@ loop invariant A == q*b + r;
        loop invariant r < b;
        loop invariant b >= B;
        loop invariant pow2(b);
        loop invariant 0 <= q <= 4294967295;
        loop invariant 0 <= r <= 4294967295;
        loop invariant 0 <= b <= 4294967295;
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
