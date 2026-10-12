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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "array_2-2.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
int main(void) {
  int A[2048] = {0};
  int B[2048] = {0};
  int i;
  int tmp;
  /*@ loop invariant 0 <= i <= 2048;
      loop invariant \forall integer t; 0 <= t < i ==> B[t] == A[t];
      loop assigns i, tmp, B[0..2047]; */
  for (i = 0; i < 2048; i++) {
    tmp = A[i];
    B[i] = tmp;
  }
  __VERIFIER_assert(A[2048/2] == B[2048/2]);
}
