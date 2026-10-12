// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array_tiling_tcpy.c", 3, "reach_error"); }
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
  assume_abort_if_not(S < 1073741823);
  int i;
  int a[2*S];
  int acopy[2*S];

  
  /*@ loop invariant 0 <= i <= S;
      loop invariant \forall integer t; 0 <= t < i ==> acopy[t] == a[t];
      loop invariant \forall integer t; 2*S-i <= t < 2*S ==> acopy[t] == a[t];
      loop assigns i, acopy[0..2*S-1]; */
  for(i=0;i < S;i++) {
    acopy[2*S - (i+1)] = a[2*S - (i+1)];
    acopy[i] = a[i];
  }

  /*@ loop invariant 0 <= i <= 2*S;
      loop invariant \forall integer t; 0 <= t < 2*S ==> acopy[t] == a[t];
      loop assigns i; */
  for(i=0;i<2*S;i++)
    __VERIFIER_assert(acopy[i] == a[i]);
  return 0;
}

