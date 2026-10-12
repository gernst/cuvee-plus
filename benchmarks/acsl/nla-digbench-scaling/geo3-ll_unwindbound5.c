// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/geo3-ll; the equality is stated modulo 2^64 since x and y are unsigned long long
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
int counter = 0;
int main() {
    int z, a, k;
    unsigned long long x, y, c;
    long long az;
    z = __VERIFIER_nondet_int();
    a = __VERIFIER_nondet_int();
    k = __VERIFIER_nondet_int();

    x = a;
    y = 1;
    c = 1;
    az = (long long) a * z;

    /*@ loop invariant (z*x - x + a - az*y) % 18446744073709551616 == 0;
        loop invariant az == a*z;
        loop invariant c >= 1;
        loop assigns x, y, c;
        loop invariant 0 <= counter <= 5; */
    while (counter++<5) {
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
