// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/ps5-ll
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "ps5-ll.c", 3, "reach_error"); }
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

int counter = 0;
int main() {
    short k;
    long long y, x, c;
    k = __VERIFIER_nondet_short();
    assume_abort_if_not(k <= 256);

    y = 0;
    x = 0;
    c = 0;

    /*@ loop invariant 6*y*y*y*y*y + 15*y*y*y*y + 10*y*y*y - 30*x - y == 0;
        loop invariant y == c;
        loop invariant 0 <= c;
        loop invariant c <= k || c == 0;
        loop assigns c, y, x;
        loop invariant 0 <= counter <= 2; */
    while (counter++<2) {
        __VERIFIER_assert(6*y*y*y*y*y + 15*y*y*y*y + 10*y*y*y - 30*x - y == 0);

        if (!(c < k))
            break;

        c = c + 1;
        y = y + 1;
        x = y * y * y * y + x;
    }

    __VERIFIER_assert(6*y*y*y*y*y + 15*y*y*y*y + 10*y*y*y - 30*x - y == 0);
    __VERIFIER_assert(k*y == y*y);
    return 0;
}
