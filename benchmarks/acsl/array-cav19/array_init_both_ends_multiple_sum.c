// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array_init_both_ends_multiple_sum.c", 3, "reach_error"); }
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
int N = 100000;
int main()
{
  int a[N];
  int b[N];
  int i;
  int sum=0;
  
  /*@ loop invariant 0 <= i <= N;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == t;
      loop assigns i, a[0..N-1]; */
  for (i=0;i<N;i++) {
    a[i] = i;
  }

  /*@ loop invariant 0 <= i <= N;
      loop invariant \forall integer t; 0 <= t < N ==> a[t] == t;
      loop invariant \forall integer t; N-i <= t < N ==> b[t] == N-1-t;
      loop assigns i, b[0..N-1]; */
  for (i=0;i<N;i++) {
    b[N-i-1]=i;
  }

  /*@ loop invariant 0 <= i <= N;
      loop invariant \forall integer t; 0 <= t < N ==> a[t] == t;
      loop invariant \forall integer t; 0 <= t < N ==> b[t] == N-1-t;
      loop invariant sum == 0;
      loop assigns i, sum; */
  for (i=0;i<N;i++) {
    sum=sum+(a[i]-b[N-i-1]);
  }

  __VERIFIER_assert(sum == 0);
  return 0;
}
