// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/hard-u; expected verdict false (d = 2*d overflows), the equalities are stated modulo 2^32
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

int counter = 0;
int main() {
    unsigned int A, B;
    unsigned int r, d, p, q;
    A = __VERIFIER_nondet_uint();
    B = __VERIFIER_nondet_uint();
    assume_abort_if_not(B >= 1);

    r = A;
    d = B;
    p = 1;
    q = 0;

    /*@ loop invariant q == 0 && r == A;
        loop invariant (d - B*p) % 4294967296 == 0;
        loop invariant p >= 1;
        loop assigns d, p;
        loop invariant 0 <= counter <= 2; */
    while (counter++<2) {
        __VERIFIER_assert(q == 0);
        __VERIFIER_assert(r == A);
        __VERIFIER_assert(d == B * p);
        if (!(r >= d)) break;

        d = 2 * d;
        p = 2 * p;
    }

    /*@ loop invariant (A - q*B - r) % 4294967296 == 0;
        loop invariant (d - B*p) % 4294967296 == 0;
        loop invariant p >= 1;
        loop assigns r, d, p, q;
        loop invariant 0 <= counter <= 2; */
    while (counter++<2) {
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
