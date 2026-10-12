// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/freire1; floating point, the invariant is exact in the reals
/* Algorithm for finding the closest integer to square root,
 * more details, see : http://www.pedrofreire.com/sqrt/sqrt1.en.html 

Note: for some reason using cpa was able to disprove these
cpa.sh -kInduction -setprop solver.solver=z3 freire1.c
*/

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "freire1.c", 10, "reach_error"); }
/*@ assigns \nothing; */
extern double __VERIFIER_nondet_double(void);
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
    int r;
    double a, x;
    a = __VERIFIER_nondet_double();
    assume_abort_if_not(a>=0 && a<=50);
    x = a / 2.0;
    r = 0;

    /*@ loop invariant r*r - a - r + 2*x == 0;
        loop invariant r >= 0;
        loop assigns x, r; */
    while (1) {
        __VERIFIER_assert((int)(r*r - a - r + 2*x) == 0);

        if (!(x > r))
            break;
        x = x - r;
        r = r + 1;
    }

    __VERIFIER_assert((int)(r*r - a - r + 2*x) == 0);
    return 0;
}
