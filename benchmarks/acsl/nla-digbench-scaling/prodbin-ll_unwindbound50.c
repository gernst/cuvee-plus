// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/prodbin-ll; y < 2^31 halves in each iteration, so it is 0 before the bound ends the loop: y < p2(31 - counter) with p2(k) = 2^k of the axiomatic P2
/* shift_add algorithm for computing the 
   product of two natural numbers
   
   This task is correct, here is an explanation why:
   - The first assertion z + x * y == (long long) a * b is a loop invariant, so it can never be violated.
   - Therefore a possible counterexample has to violate the assertion __VERIFIER_assert(z == (long long) a * b); after the loop.
   - However we need to execute the loop completely, because the condition !(y != 0) together with the loop invariant implies the second assertion.
   - Therefore y must always be greater than zero.
   - y is divided by 2 in every iteration, therefore b >= 2^49 (since b is the initial value of y).
   - However, b has the type int, therefore b < 2^31.
   - That concludes that there is no counterexample and the program is correct.
*/
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "prodbin-ll.c", 15, "reach_error"); }
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
/*@ axiomatic P2 {
  logic integer p2(integer k);
  axiom p2_zero: p2(0) == 1;
  axiom p2_step: \forall integer k; k > 0 ==> p2(k) == 2*p2(k-1);
} */
int main() {
    int a, b;
    long long x, y, z;

    a = __VERIFIER_nondet_int();
    b = __VERIFIER_nondet_int();
    assume_abort_if_not(b >= 1);

    x = a;
    y = b;
    z = 0;

    /*@ loop invariant z + x*y == a*b;
        loop invariant y >= 0;
        loop invariant counter <= 31 ==> y < p2(31 - counter);
        loop invariant counter > 31 ==> y == 0;
        loop assigns x, y, z, counter;
        loop invariant 0 <= counter <= 50; */
    while (counter++<50) {
        __VERIFIER_assert(z + x * y == (long long) a * b);
        if (!(y != 0))
            break;

        if (y % 2 == 1) {
            z = z + x;
            y = y - 1;
        }
        x = 2 * x;
        y = y / 2;
    }
    __VERIFIER_assert(z == (long long) a * b);
    
    return 0;
}
