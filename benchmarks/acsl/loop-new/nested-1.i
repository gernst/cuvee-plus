// ACSL annotations added by hand (benchmarks/acsl/README.md)
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "assert.h", 3, __extension__ __PRETTY_FUNCTION__); })); }
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
  ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();
int main() {
    int n = __VERIFIER_nondet_int();
    int m = __VERIFIER_nondet_int();
    int k = 0;
    int i,j;
    if (!(10 <= n && n <= 10000)) return 0;
    if (!(10 <= m && m <= 10000)) return 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant k == i*m;
        loop assigns i, j, k; */
    for (i = 0; i < n; i++) {
 /*@ loop invariant 0 <= j <= m;
     loop invariant k == i*m + j;
     loop assigns j, k; */
 for (j = 0; j < m; j++) {
     k ++;
 }
    }
    __VERIFIER_assert(k >= 100);
    return 0;
}
