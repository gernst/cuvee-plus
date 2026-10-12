// ACSL annotations added by hand (benchmarks/acsl/README.md)
extern void *malloc (unsigned int __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;
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
extern int __VERIFIER_nondet_int();
extern void *malloc(unsigned int size);
int main() {
    int n = __VERIFIER_nondet_int();
    if (!(0 <= n && n <= 1000)) return 0;
    int *x = malloc(n * sizeof(int));
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer t; 0 <= t < i ==> x[t] == 0;
        loop assigns i, x[0..n-1]; */
    for (int i = 0; i < n; i++) x[i] = 0;
    /*@ loop invariant 0 <= i <= n;
        loop invariant \forall integer t; 0 <= t < n ==> x[t] == 0;
        loop assigns i; */
    for (int i = 0; i < n; i++) __VERIFIER_assert(x[i] == 0);
    return 0;
}
