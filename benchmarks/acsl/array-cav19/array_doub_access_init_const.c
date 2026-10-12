// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array_doub_access_init_const.c", 3, "reach_error"); }
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
int main()
{
  int i;
  int N=100000;
  int a[2*N+2];

  /*@ loop invariant 0 <= i <= N+1;
      loop invariant \forall integer t; 0 <= t < 2*i ==> a[t] == 0;
      loop assigns i, a[0..2*N+1]; */
  for(i=0;i<=N;i++) {
    a[2*i]=0;
    a[2*i+1]=0;
  }

  /*@ loop invariant 0 <= i <= 2*N+1;
      loop invariant \forall integer t; 0 <= t < 2*N+2 ==> a[t] == 0;
      loop assigns i; */
  for(i=0;i<=2*N;i++)
    __VERIFIER_assert(a[i]>=0);
  return 0;
}
