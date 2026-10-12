// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "for_infinite_loop_1.c", 3, "reach_error"); }

extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
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

int main() {
  unsigned int i=0;
  int x=0, y=0;
  int n=__VERIFIER_nondet_int();
  if (!(n>0)) return 0;
  /*@ loop invariant x == 0;
      loop assigns i; */
  for(i=0; 1; i++)
  {
    __VERIFIER_assert(x==0);
  }
  __VERIFIER_assert(x==0);
}

