// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/hard-u; the equalities are exact, with bounds on d, p, q that exclude the wrap-around, since A and B are bounded; p is a power of 2 by the predicate pow2 of the axiomatic Pow2
/*
  hardware integer division program, by Manna
  returns q==A//B
  */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "hard-u.c", 8, "reach_error"); }
/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint(void);
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
    unsigned int A, B;
    unsigned int r, d, p, q;
    A = __VERIFIER_nondet_uint();
    assume_abort_if_not(A>=0 && A<=50);
    B = __VERIFIER_nondet_uint();
    assume_abort_if_not(B>=0 && B<=50);
    assume_abort_if_not(B >= 1);

    r = A;
    d = B;
    p = 1;
    q = 0;

    /*@ loop invariant q == 0 && r == A;
        loop invariant d == B*p;
        loop invariant pow2(p);
        loop invariant p <= d && d <= B + 2*A;
        loop assigns d, p; */
    while (1) {
        __VERIFIER_assert(q == 0);
        __VERIFIER_assert(r == A);
        __VERIFIER_assert(d == B * p);
        if (!(r >= d)) break;

        d = 2 * d;
        p = 2 * p;
    }

    /*@ loop invariant A == q*B + r;
        loop invariant d == B*p;
        loop invariant r < d;
        loop invariant pow2(p);
        loop invariant p <= d && d <= B + 2*A;
        loop invariant q <= A;
        loop assigns r, d, p, q; */
    while (1) {
        __VERIFIER_assert(A == q*B + r);
        __VERIFIER_assert(d == B*p);

        if (!(p != 1)) break;

        d = d / 2;
        p = p / 2;
        if (r >= d) {
            r = r - d;
            q = q + p;
        }
    }

    __VERIFIER_assert(A == d*q + r);
    __VERIFIER_assert(B == d);    
    return 0;
}
