// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/geo3-ll; the equality is exact, since x and y are signed long long here, whose overflow is undefined and not modelled
/* 
Geometric Series
computes x = sum(z^k)[k=0..k-1], y = z^(k-1)
*/

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "geo3-ll.c", 8, "reach_error"); }
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
    int z, a, k;
    long long x, y, c, az;
    z = __VERIFIER_nondet_int();
    assume_abort_if_not(z>=0 && z<=1);
    a = __VERIFIER_nondet_int();
    assume_abort_if_not(a>=0 && a<=1);
    k = __VERIFIER_nondet_int();
    assume_abort_if_not(k>=0 && k<=1);

    x = a;
    y = 1;
    c = 1;
    az = (long long) a * z;

    /*@ loop invariant z*x - x + a - az*y == 0;
        loop invariant az == a*z;
        loop invariant c >= 1;
        loop assigns x, y, c; */
    while (1) {
        __VERIFIER_assert(z*x - x + a - az*y == 0);

        if (!(c < k))
            break;

        c = c + 1;
        x = x * z + a;
        y = y * z;
    }
    __VERIFIER_assert(z*x - x + a - az*y == 0);
    return x;
}
