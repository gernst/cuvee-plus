// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/divbin; expected verdict false (b = 2*b overflows), the invariants are those of divbin2
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "divbin.c", 10, __extension__ __PRETTY_FUNCTION__); })); }
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
int main() {
  unsigned A, B;
  unsigned q, r, b;
    A = __VERIFIER_nondet_uint();
    assume_abort_if_not(A>=0 && A<=2);
    B = __VERIFIER_nondet_uint();
    assume_abort_if_not(B>=0 && B<=2);
    assume_abort_if_not(B < (0x7fffffff * 2U + 1U)/2);
    assume_abort_if_not(B >= 1);
    q = 0;
    r = A;
    b = B;
    /*@ loop invariant q == 0 && r == A;
        loop invariant b >= B;
        loop invariant \exists integer k; 0 <= k <= 64 && b == B * (1 << k);
        loop assigns b; */
    while (1) {
        if (!(r >= b)) break;
        b = 2 * b;
    }
    /*@ loop invariant A == q*b + r;
        loop invariant r < b;
        loop invariant b >= B;
        loop invariant \exists integer k; 0 <= k <= 64 && b == B * (1 << k);
        loop assigns q, r, b; */
    while (1) {
        __VERIFIER_assert(A == q * b + r);
        if (!(b != B)) break;
        q = 2 * q;
        b = b / 2;
        if (r >= b) {
            q = q + 1;
            r = r - b;
        }
    }
    __VERIFIER_assert(A == q * b + r);
    return 0;
}
