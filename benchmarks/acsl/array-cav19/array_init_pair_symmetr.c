// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array_init_pair_symmetr.c", 3, "reach_error"); }
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
int N = 100000;
int main()
{
  int i;
  int a[N];
  int b[N];
  int c[N];

  /*@ loop invariant 0 <= i <= N;
      loop invariant \forall integer t; 0 <= t < i ==> b[t] == -a[t];
      loop assigns i, a[0..N-1], b[0..N-1]; */
  for(i=0;i<N;i++) {
    int x=__VERIFIER_nondet_int();
    assume_abort_if_not(x > -100000 && x < 100000);
    a[i]=x;
    b[i]=-x;
  }

  /*@ loop invariant 0 <= i <= N;
      loop invariant \forall integer t; 0 <= t < N ==> b[t] == -a[t];
      loop invariant \forall integer t; 0 <= t < i ==> c[t] == 0;
      loop assigns i, c[0..N-1]; */
  for(i=0;i<N;i++){
    c[i]=a[i]+b[i];
  }

  /*@ loop invariant 1 <= i <= N;
      loop invariant \forall integer t; 0 <= t < N ==> c[t] == 0;
      loop assigns i; */
  for(i=1;i<N;i++)
    __VERIFIER_assert(c[i] == 0);
  return 0;
}
