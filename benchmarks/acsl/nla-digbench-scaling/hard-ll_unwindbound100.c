// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/hard-ll; p is a power of 2, written with a shift
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
void reach_error() { __assert_fail("0", "hard-ll.c", 8, "reach_error"); }
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
    long long r, d, p, q;
    A = __VERIFIER_nondet_uint();
    B = __VERIFIER_nondet_uint();
    assume_abort_if_not(B >= 1);

    r = A;
    d = B;
    p = 1;
    q = 0;

    /*@ loop invariant q == 0 && r == A;
        loop invariant d == B*p;
        loop invariant p >= 1;
        loop invariant \exists integer k; 0 <= k <= 64 && p == 1 * (1 << k);
        loop assigns d, p;
        loop invariant 0 <= counter <= 100; */
    while (counter++<100) {
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
        loop invariant r >= 0;
        loop invariant p >= 1;
        loop invariant \exists integer k; 0 <= k <= 64 && p == 1 * (1 << k);
        loop assigns r, d, p, q;
        loop invariant 0 <= counter <= 100; */
    while (counter++<100) {
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
