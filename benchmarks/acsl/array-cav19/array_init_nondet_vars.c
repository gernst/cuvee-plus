// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array_init_nondet_vars.c", 3, "reach_error"); }
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
  int n=__VERIFIER_nondet_int();
  assume_abort_if_not(n < 100000);
  int a[n];

  assume_abort_if_not(j>0 && j < 10000);
 
  /*@ loop invariant 1 <= i && (i <= n || i == 1);
      loop invariant \forall integer t; 1 <= t < i ==> a[t] >= t+2;
      loop assigns i, a[1..n-1]; */
  for(i=1;i<n;i++) {
    int k=__VERIFIER_nondet_int();
    assume_abort_if_not(k>0 && k < 10000);
    a[i]=i+j+k;
  }

  /*@ loop invariant 1 <= i && (i <= n || i == 1);
      loop invariant \forall integer t; 1 <= t < n ==> a[t] >= t+2;
      loop assigns i; */
  for(i=1;i<n;i++)
    __VERIFIER_assert(a[i]>=(i+2));
  return 0;
}  
