// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/lcm1; the equality is stated modulo 2^32 since the variables are unsigned
/*
 * algorithm for computing simultaneously the GCD and the LCM,
 * by Sankaranarayanan
 */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "lcm1.c", 8, "reach_error"); }
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
    assume_abort_if_not(a >= 1);  //infinite loop if remove
    assume_abort_if_not(b >= 1);

    assume_abort_if_not(a <= 65535);
    assume_abort_if_not(b <= 65535);

    x = a;
    y = b;
    u = b;
    v = 0;

    /*@ loop invariant (x*u + y*v - a*b) % 4294967296 == 0;
        loop invariant x >= 1 && y >= 1;
        loop assigns x, y, u, v;
        loop invariant 0 <= counter <= 5 + 1; */
    while (counter++<5) {
        __VERIFIER_assert(x*u + y*v == a*b);
        if (!(x != y))
            break;

        /*@ loop invariant (x*u + y*v - a*b) % 4294967296 == 0;
            loop invariant x >= 1 && y >= 1;
            loop assigns x, y, u, v;
            loop invariant 0 <= counter <= 5; */
        while (counter++<5) {
	    __VERIFIER_assert(x*u + y*v == a*b);
            if (!(x > y))
                break;
            x = x - y;
            v = v + u;
        }

        /*@ loop invariant (x*u + y*v - a*b) % 4294967296 == 0;
            loop invariant x >= 1 && y >= 1;
            loop assigns x, y, u, v;
            loop invariant 0 <= counter <= 5; */
        while (counter++<5) {
	    __VERIFIER_assert(x*u + y*v == a*b);
            if (!(x < y))
                break;
            y = y - x;
            u = u + v;
        }
    }

    __VERIFIER_assert(u*y + v*y == a*b);
    __VERIFIER_assert(x == y);

    //x == gcd(a,b)
    //u + v == lcm(a,b)
    return 0;
}
