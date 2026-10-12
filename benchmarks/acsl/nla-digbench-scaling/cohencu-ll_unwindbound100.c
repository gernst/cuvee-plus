// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/cohencu-ll
/*
Printing consecutive cubes, by Cohen
http://www.cs.upc.edu/~erodri/webpage/polynomial_invariants/cohencu.htm
*/

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "cohencu-ll.c", 8, "reach_error"); }
/*@ assigns \nothing; */
extern unsigned short __VERIFIER_nondet_ushort(void);
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
    short a;
    long long n, x, y, z;
    a = __VERIFIER_nondet_ushort();

    n = 0;
    x = 0;
    y = 1;
    z = 6;

    /*@ loop invariant z == 6*n + 6;
        loop invariant y == 3*n*n + 3*n + 1;
        loop invariant x == n*n*n;
        loop invariant n >= 0;
        loop invariant n <= a + 1 || n == 0;
        loop assigns n, x, y, z;
        loop invariant 0 <= counter <= 100; */
    while (counter++<100) {
        __VERIFIER_assert(z == 6 * n + 6);
        __VERIFIER_assert(y == 3 * n * n + 3 * n + 1);
        __VERIFIER_assert(x == n * n * n);
	__VERIFIER_assert(y*z - 18*x - 12*y + 2*z - 6 == 0);
	__VERIFIER_assert((z*z) - 12*y - 6*z + 12 == 0);
        if (!(n <= a))
            break;

        n = n + 1;
        x = x + y;
        y = y + z;
        z = z + 6;
    }

    __VERIFIER_assert(z == 6*n + 6);
    __VERIFIER_assert(6*a*x - x*z + 12*x == 0);
    __VERIFIER_assert(a*z - 6*a - 2*y + 2*z - 10 == 0);
    __VERIFIER_assert(2*y*y - 3*x*z - 18*x - 10*y + 3*z - 10 == 0);
    __VERIFIER_assert(z*z - 12*y - 6*z + 12 == 0);
    __VERIFIER_assert(y*z - 18*x - 12*y + 2*z - 6 == 0);
    
    return 0;
}
