// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array_init_var_plus_ind.c", 3, "reach_error"); }
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
  int j=0;
  int a[N];

  /*@ loop invariant 0 <= i <= N;
      loop invariant 2*j == i*(i-1);
      loop invariant \forall integer t; 0 <= t < i ==> 2*a[t] == t*(t-1);
      loop assigns i, j, a[0..N-1]; */
  for(i=0;i<N;i++){
    int x=__VERIFIER_nondet_int();
    if(x) break;
    a[i]=j;
    j=j+i;
  }

  /*@ loop invariant 1 <= k && (k <= i || k == 1);
      loop invariant \forall integer t; 0 <= t < i ==> a[t] >= 0;
      loop assigns k; */
  for(int k=1;k<i;k++)
    __VERIFIER_assert(a[k]>=0);
  return 0;
}

