// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (eval sets x to 1)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "while_infinite_loop_4.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int x=0;

/*@ assigns x;
    ensures x == 1; */
void eval(void) 
{
  /*@ loop assigns x; */
  while (1) {
      x=1;
      break;
  }
  return;
}


int main() {

  /*@ loop invariant 0 <= x <= 1;
      loop assigns x; */
  while(1)
  {
    eval();
    __VERIFIER_assert(x==0);    
  }

  __VERIFIER_assert(x==0);

  return 0;
}

