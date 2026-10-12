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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "sum_array-2-2.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint();
int main()
{
  unsigned int M = __VERIFIER_nondet_uint();
  if (M > 1000000) {
    return 0;
  }
  int A[M], B[M], C[M];
  unsigned int i;
  /*@ loop invariant 0 <= i <= M;
      loop assigns i, A[0..M-1]; */
  for(i=0;i<M;i++) {
    A[i] = __VERIFIER_nondet_int();
    if (!(A[i] <= 1000000)) return 0;
    if (!(A[i] >= -1000000)) return 0;
  }
  /*@ loop invariant 0 <= i <= M;
      loop assigns i, B[0..M-1]; */
  for(i=0;i<M;i++) {
    B[i] = __VERIFIER_nondet_int();
    if(!(B[i] <= 1000000)) return 0;
    if(!(B[i] >= -1000000)) return 0;
  }
  /*@ loop invariant 0 <= i <= M;
      loop invariant \forall integer t; 0 <= t < i ==> C[t] == A[t] + B[t];
      loop assigns i, C[0..M-1]; */
  for(i=0;i<M;i++)
     C[i]=A[i]+B[i];
  /*@ loop invariant 0 <= i <= M;
      loop invariant \forall integer t; 0 <= t < M ==> C[t] == A[t] + B[t];
      loop assigns i; */
  for(i=0;i<M;i++)
     __VERIFIER_assert(C[i]==A[i]+B[i]);
}
