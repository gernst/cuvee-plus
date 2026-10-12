// ACSL annotations added by hand (benchmarks/acsl/README.md)
int SIZE = 50000001;


/*@ assigns \nothing; */
int __VERIFIER_nondet_int();
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "loopv1.c", 7, "reach_error"); }
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


int main() {
  int n,i,j;
  n = __VERIFIER_nondet_int();
  if (!(n <= SIZE)) return 0;
  i = 0; j=0;
  /*@ loop invariant i % 3 == 0;
      loop assigns i; */
  while(i<n){ 
 
    if(__VERIFIER_nondet_int())	  
      i = i + 6; 
    else
     i = i + 3;    
  }
  __VERIFIER_assert( (i%3) == 0 );
  return 0;
}
