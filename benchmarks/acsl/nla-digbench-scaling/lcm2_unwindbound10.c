// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/lcm2; the equality is stated modulo 2^32, since 2*a*b and u + v exceed 2^32, by the logic function l2(x, y, u, v, a, b), which stands for (x*u + y*v - 2*a*b) % 2^32, characterized by trusted lemmas only (a definition makes z3 give up on the other goals): l2_init, l2_left and l2_right, the steps of the branches keep x*u + y*v, and l2_value, the assertion in C
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
/*@ axiomatic Lcm2 {
  logic integer l2(integer x, integer y, integer u, integer v, integer a, integer b);
  lemma l2_init: \forall integer a, b; l2(a, b, b, a, a, b) == 0;
  lemma l2_left: \forall integer x, y, u, v, a, b; l2(x, y, u, v, a, b) == 0 ==>
    l2((unsigned int)(x - y), y, u, (unsigned int)(v + u), a, b) == 0;
  lemma l2_right: \forall integer x, y, u, v, a, b; l2(x, y, u, v, a, b) == 0 ==>
    l2(x, (unsigned int)(y - x), (unsigned int)(u + v), v, a, b) == 0;
  lemma l2_value: \forall integer x, y, u, v, a, b; l2(x, y, u, v, a, b) == 0 ==>
    (unsigned int)((unsigned int)(x*u) + (unsigned int)(y*v)) == (unsigned int)((unsigned int)(2*a)*b);
} */
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

    /*@ loop invariant l2(x, y, u, v, a, b) == 0;
        loop invariant 1 <= x <= 4294967295 && 1 <= y <= 4294967295;
        loop invariant 0 <= u <= 4294967295 && 0 <= v <= 4294967295;
        loop assigns x, y, u, v, counter;
        loop invariant 0 <= counter <= 10; */
    while (counter++<10) {
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
