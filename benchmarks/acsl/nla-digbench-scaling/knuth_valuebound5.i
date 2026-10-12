// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/knuth; the asserted equalities modulo 2^32 (unsigned variables); sqrt is a floating point call
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

/*@ requires \false;
    assigns \nothing; */
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "knuth.c", 7, __extension__ __PRETTY_FUNCTION__); })); }
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
extern double sqrt(double);
int main() {
    unsigned n, a;
    unsigned r, k, q, d, s, t;
    n = __VERIFIER_nondet_uint();
    assume_abort_if_not(n>=0 && n<=5);
    a = __VERIFIER_nondet_uint();
    assume_abort_if_not(a>=0 && a<=5);
    assume_abort_if_not(n < (0x7fffffff * 2U + 1U)/8);
    assume_abort_if_not(a > 2);
    d = a;
    r = n % d;
    t = 0;
    k = n % (d - 2);
    q = 4 * (n / (d - 2) - n / d);
    s = sqrt(n);
    /*@ loop invariant (d*d*q - 2*q*d - 4*r*d + 4*k*d + 8*r - 8*n) % 4294967296 == 0;
        loop invariant (k*t - t*t) % 4294967296 == 0;
        loop invariant (d*d*q - 2*d*q - 4*d*r + 4*d*t + 4*a*k - 4*a*t - 8*n + 8*r) % 4294967296 == 0;
        loop invariant (d*k - d*t - a*k + a*t) % 4294967296 == 0;
        loop assigns r, k, q, d, t; */
    while (1) {
        __VERIFIER_assert(d * d * q - 2 * q * d - 4 * r * d + 4 * k * d + 8 * r == 8 * n);
        __VERIFIER_assert(k * t == t * t);
        __VERIFIER_assert(d * d * q - 2 * d * q - 4 * d * r + 4 * d * t + 4 * a * k - 4 * a * t - 8 * n + 8 * r == 0);
        __VERIFIER_assert(d * k - d * t - a * k + a * t == 0);
        if (!((s >= d) && (r != 0))) break;
        if (2 * r + q < k) {
            t = r;
            r = 2 * r - k + q + d + 2;
            k = t;
            q = q + 4;
            d = d + 2;
        } else if ((2 * r + q >= k) && (2 * r + q < d + k + 2)) {
            t = r;
            r = 2 * r - k + q;
            k = t;
            d = d + 2;
        } else if ((2 * r + q >= k) && (2 * r + q >= d + k + 2) && (2 * r + q < 2 * d + k + 4)) {
            t = r;
            r = 2 * r - k + q - d - 2;
            k = t;
            q = q - 4;
            d = d + 2;
        } else {
            t = r;
            r = 2 * r - k + q - 2 * d - 4;
            k = t;
            q = q - 8;
            d = d + 2;
        }
    }
    return 0;
}
