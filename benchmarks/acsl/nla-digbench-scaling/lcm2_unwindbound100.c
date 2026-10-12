// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/lcm2; the equality is stated modulo 2^32 since the variables are unsigned
/* Algorithm for computing simultaneously the GCD and the LCM, by Dijkstra */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "lcm2.c", 5, "reach_error"); }
/*@ assigns \nothing; */
extern unsigned __VERIFIER_nondet_uint(void);
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
    unsigned a, b;
    unsigned x, y, u, v;
    a = __VERIFIER_nondet_uint();
    b = __VERIFIER_nondet_uint();
    assume_abort_if_not(a >= 1); //inf loop if remove
    assume_abort_if_not(b >= 1);

    assume_abort_if_not(a <= 65535);
    assume_abort_if_not(b <= 65535);

    x = a;
    y = b;
    u = b;
    v = a;

    /*@ loop invariant (x*u + y*v - 2*a*b) % 4294967296 == 0;
        loop invariant x >= 1 && y >= 1;
        loop assigns x, y, u, v;
        loop invariant 0 <= counter <= 100; */
    while (counter++<100) {
        __VERIFIER_assert(x*u + y*v == 2*a*b);

        if (!(x != y))
            break;

        if (x > y) {
            x = x - y;
            v = v + u;
        } else {
            y = y - x;
            u = u + v;
        }
    }

    __VERIFIER_assert(x*u + y*v == 2*a*b);
    // x == gcd(a,b)
    //(u + v)/2==lcm(a,b)

    return 0;
}
