// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/geo1-ll; the equality is stated modulo 2^64 since x and y are unsigned long long
/* 
Geometric Series
computes x=(z-1)* sum(z^k)[k=0..k-1] , y = z^k
returns 1+x-y == 0
*/

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "geo1-ll.c", 9, "reach_error"); }
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
    int z, k;
    unsigned long long x, y, c;
    z = __VERIFIER_nondet_int();
    k = __VERIFIER_nondet_int();
    assume_abort_if_not(z >= 1);
    assume_abort_if_not(k >= 1);

    x = 1;
    y = z;
    c = 1;

    /*@ loop invariant (x*z - x - y + 1) % 18446744073709551616 == 0;
        loop invariant c >= 1;
        loop assigns x, y, c, counter;
        loop invariant 0 <= counter <= 100; */
    while (counter++<100) {
        __VERIFIER_assert(x*z - x - y + 1 == 0);

        if (!(c < k)) 
            break;

        c = c + 1;
        x = x * z + 1;
        y = y * z;

    }  //geo1

    x = x * (z - 1);

    __VERIFIER_assert(1 + x - y == 0);
    return 0;
}
