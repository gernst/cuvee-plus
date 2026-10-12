// ACSL annotations added by hand (benchmarks/acsl/README.md): the assertion is the negation of the loop condition; the ranges of the unsigned variables that the loops assign are loop invariants
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "trex03-2.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
unsigned int __VERIFIER_nondet_uint();
/*@ assigns \nothing; */
_Bool __VERIFIER_nondet_bool();

int main()
{
  unsigned int x1=__VERIFIER_nondet_uint(), x2=__VERIFIER_nondet_uint(), x3=__VERIFIER_nondet_uint();
  unsigned int d1=1, d2=1, d3=1;
  _Bool c1=__VERIFIER_nondet_bool(), c2=__VERIFIER_nondet_bool();
  
  /*@ loop invariant d1 == 1 && d2 == 1 && d3 == 1;
      loop invariant 0 <= x1 <= 4294967295;
      loop invariant 0 <= x2 <= 4294967295;
      loop invariant 0 <= x3 <= 4294967295;
      loop assigns x1, x2, x3, c1, c2; */
  while(x1>0 && x2>0 && x3>0)
  {
    if (c1) x1=x1-d1;
    else if (c2) x2=x2-d2;
    else x3=x3-d3;
    c1=__VERIFIER_nondet_bool();
    c2=__VERIFIER_nondet_bool();
  }

  __VERIFIER_assert(x1==0 || x2==0 || x3==0);
  return 0;
}

