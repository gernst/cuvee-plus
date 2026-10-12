// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (the first zero may lie beyond the middle)
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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "array_3-2.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
int main(void) {
  int A[1024];
  int i;
  /*@ loop invariant 0 <= i <= 1024;
      loop assigns i, A[0..1023]; */
  for (i = 0; i < 1024; i++) {
    A[i] = __VERIFIER_nondet_int();
  }
  /*@ loop invariant 0 <= i <= 1024;
      loop assigns i; */
  for (i = 0; i < 1024 && A[i] != 0; i++) {
  }
  __VERIFIER_assert(i <= 1024 / 2);
}
