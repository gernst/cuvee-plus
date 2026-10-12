// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/mannadiv
/* 
 Division algorithm from
 "Z. Manna, Mathematical Theory of Computation, McGraw-Hill, 1974"
 return x1 // x2
*/

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "mannadiv.c", 9, "reach_error"); }
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
    int x1, x2;
    int y1, y2, y3;
    x1 = __VERIFIER_nondet_int();
    x2 = __VERIFIER_nondet_int();

    assume_abort_if_not(x1 >= 0);
    assume_abort_if_not(x2 != 0);

    y1 = 0;
    y2 = 0;
    y3 = x1;

    /*@ loop invariant y1*x2 + y2 + y3 == x1;
        loop invariant y3 >= 0;
        loop assigns y1, y2, y3;
        loop invariant 0 <= counter <= 1; */
    while (counter++<1) {
        __VERIFIER_assert(y1*x2 + y2 + y3 == x1);

        if (!(y3 != 0)) break;

        if (y2 + 1 == x2) {
            y1 = y1 + 1;
            y2 = 0;
            y3 = y3 - 1;
        } else {
            y2 = y2 + 1;
            y3 = y3 - 1;
        }
    }
    __VERIFIER_assert(y1*x2 + y2 == x1);
    return 0;
}
