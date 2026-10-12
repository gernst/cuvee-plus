// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array_min_and_copy_shift_sum_add.c", 3, "reach_error"); }
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();
int main()
{
  int i;
  int j=__VERIFIER_nondet_int();
  assume_abort_if_not(j < 10000 && j > -10000);
  int k = 0;
  int N=__VERIFIER_nondet_int();
  assume_abort_if_not(N < 10000 && N > -10000);
  int a[N+1];
  int b[N];

  /*@ loop invariant 0 <= i && (i <= N || i == 0);
      loop invariant \forall integer t; 0 <= t < i ==> j <= a[t];
      loop assigns i, j; */
  for(i=0;i<N;i++) {
    assume_abort_if_not(a[i] < 10000 && a[i] > -10000);
    if (j > a[i])
      j = a[i];
  }

  /*@ loop invariant 0 <= i && (i <= N || i == 0);
      loop invariant \forall integer t; 0 <= t < N ==> j <= a[t];
      loop invariant \forall integer t; 0 <= t < i ==> b[t] == a[t] - j;
      loop assigns i, b[0..N-1]; */
  for(i=0;i<N;i++) {
    b[i] = a[i]-j;
  }

  /*@ loop invariant 0 <= i && (i <= N || i == 0);
      loop invariant \forall integer t; 0 <= t < N ==> b[t] >= 0;
      loop invariant k >= 0;
      loop assigns i, k; */
  for(i=0;i<N;i++) {
    k = k+b[i]+i;
  }
      
  __VERIFIER_assert(k >= 0);
  return 0;
}
