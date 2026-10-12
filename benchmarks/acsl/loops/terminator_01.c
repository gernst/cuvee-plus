// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (the loop terminates and 0 is asserted)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "terminator_01.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();

int main()
{
  int x=__VERIFIER_nondet_int();
  int *p = &x;
 
  /*@ loop invariant p == &x;
      loop assigns x; */
  while(x<100) {
   (*p)++;
  }                       
  __VERIFIER_assert(0);    

  return 0;
}

