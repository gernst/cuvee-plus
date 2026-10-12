// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/dijkstra-u; q is a power of 4, written with a shift; the equalities are stated modulo 2^32 since the variables are unsigned
/* Compute the floor of the square root, by Dijkstra */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "dijkstra-u.c", 5, "reach_error"); }
/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint(void);
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
    unsigned int n, p, q, r, h;

    n = __VERIFIER_nondet_uint();
    assume_abort_if_not(n < 4294967295 / 4);  // Avoid non-terminating loop

    p = 0;
    q = 1;
    r = n;
    h = 0;
    /*@ loop invariant p == 0 && r == n && h == 0;
        loop invariant q >= 1;
        loop invariant \exists integer k; 0 <= k <= 64 && q == 1 * (1 << k);
        loop invariant q % 4 == 0 || q == 1;
        loop assigns q;
        loop invariant 0 <= counter <= 20; */
    while (counter++<20) {
        if (!(q <= n))
            break;

        q = 4 * q;
    }
    //q == 4^n

    /*@ loop invariant (p*p + r*q - n*q) % 4294967296 == 0;
        loop invariant r < 2*p + q;
        loop invariant (h*h*h - 12*h*n*q + 16*n*p*q - h*q*q - 4*p*q*q + 12*h*q*r - 16*p*q*r) % 4294967296 == 0;
        loop invariant (h*h*n - 4*h*n*p + 4*(n*n)*q - n*q*q - h*h*r + 4*h*p*r - 8*n*q*r + q*q*r + 4*q*r*r) % 4294967296 == 0;
        loop invariant (h*h*p - 4*h*n*q + 4*n*p*q - p*q*q + 4*h*q*r - 4*p*q*r) % 4294967296 == 0;
        loop invariant q >= 1;
        loop invariant \exists integer k; 0 <= k <= 64 && q == 1 * (1 << k);
        loop invariant q % 4 == 0 || q == 1;
        loop assigns p, q, r, h;
        loop invariant 0 <= counter <= 20; */
    while (counter++<20) {
        __VERIFIER_assert(r < 2 * p + q);
        __VERIFIER_assert(p*p + r*q == n*q);
        __VERIFIER_assert(h * h * h - 12 * h * n * q + 16 * n * p * q - h * q * q - 4 * p * q * q + 12 * h * q * r - 16 * p * q * r == 0);
        __VERIFIER_assert(h * h * n - 4 * h * n * p + 4 * (n * n) * q - n * q * q - h * h * r + 4 * h * p * r - 8 * n * q * r + q * q * r + 4 * q * r * r == 0);
        __VERIFIER_assert(h * h * p - 4 * h * n * q + 4 * n * p * q - p * q * q + 4 * h * q * r - 4 * p * q * r == 0);
        __VERIFIER_assert(p * p - n * q + q * r == 0);

        if (!(q != 1))
            break;

        q = q / 4;
        h = p + q;
        p = p / 2;
        if (r >= h) {
            p = p + q;
            r = r - h;
        }
    }
    __VERIFIER_assert(h*h*h - 12*h*n + 16*n*p + 12*h*r - 16*p*r - h - 4*p == 0);
    __VERIFIER_assert(p*p - n + r == 0);
    __VERIFIER_assert(h*h*p - 4*h*n + 4*n*p + 4*h*r - 4*p*r - p == 0);
    return 0;
}
