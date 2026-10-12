// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/sqrt1-ll
/* Compute the floor of the square root of a natural number */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "sqrt1-ll.c", 5, "reach_error"); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
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


int main() {
    int n;
    long long a, s, t;
    n = __VERIFIER_nondet_int();
    assume_abort_if_not(n>=0 && n<=1);

    a = 0;
    s = 1;
    t = 1;

    /*@ loop invariant t == 2*a + 1;
        loop invariant s == (a + 1)*(a + 1);
        loop invariant a >= 0;
        loop assigns a, s, t; */
    while (1) {
        __VERIFIER_assert(t == 2*a + 1);
        __VERIFIER_assert(s == (a + 1) * (a + 1));
	__VERIFIER_assert(t*t - 4*s + 2*t + 1 == 0);
        // the above 2 should be equiv to 

        if (!(s <= n))
            break;

        a = a + 1;
        t = t + 2;
        s = s + t;
    }
    
    __VERIFIER_assert(t == 2 * a + 1);
    __VERIFIER_assert(s == (a + 1) * (a + 1));
    __VERIFIER_assert(t*t - 4*s + 2*t + 1 == 0);

    return 0;
}
