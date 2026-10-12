// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array_tiling_poly6.c", 3, "reach_error"); }
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
  int S=__VERIFIER_nondet_int();
  assume_abort_if_not(S>1);
  long long i;
  long long a[S];

  /*@ loop invariant 0 <= i <= S;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == (t-1)*(t+1);
      loop assigns i, a[0..S-1]; */
  for(i=0;i<S;i++)
    a[i]=((i-1)*(i+1));

  /*@ loop invariant 0 <= i <= S;
      loop invariant \forall integer t; 0 <= t < i ==> a[t] == -1;
      loop invariant \forall integer t; i <= t < S ==> a[t] == (t-1)*(t+1);
      loop assigns i, a[0..S-1]; */
  for(i=0;i<S;i++)
    a[i]=a[i]-(i*i);

  /*@ loop invariant 0 <= i <= S;
      loop invariant \forall integer t; 0 <= t < S ==> a[t] == -1;
      loop assigns i; */
  for(i=0;i<S;i++)
    __VERIFIER_assert(a[i]==-1);
  return 0;
}

