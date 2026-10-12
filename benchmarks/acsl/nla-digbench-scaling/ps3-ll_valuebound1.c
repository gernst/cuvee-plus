// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/ps3-ll
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "ps3-ll.c", 3, "reach_error"); }
/*@ assigns \nothing; */
extern short __VERIFIER_nondet_short(void);
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
    short k; 
    long long y, x, c;
    k = __VERIFIER_nondet_short();
    assume_abort_if_not(k>=0 && k<=1);

    y = 0;
    x = 0;
    c = 0;

    /*@ loop invariant 6*x - 2*y*y*y - 3*y*y - y == 0;
        loop invariant y == c;
        loop invariant 0 <= c;
        loop invariant c <= k || c == 0;
        loop assigns c, y, x; */
    while (1) {
        __VERIFIER_assert(6*x - 2*y*y*y - 3*y*y - y == 0);

        if (!(c < k))
            break;

        c = c + 1;
        y = y + 1;
        x = y * y + x;
    }
    __VERIFIER_assert(6*x - 2*y*y*y - 3*y*y - y == 0);
    return 0;
}
