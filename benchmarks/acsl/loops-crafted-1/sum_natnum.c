// ACSL annotations added by hand (benchmarks/acsl/README.md)
int SIZE = 40000; 


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
void reach_error() { __assert_fail("0", "sum_natnum.c", 7, "reach_error"); }
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
  int i;
  unsigned long long sum;
  i = 0, sum =0; 
  /*@ loop invariant 0 <= i <= SIZE;
      loop invariant 2*sum == i*(i+1);
      loop assigns i, sum; */
  while(i< SIZE){ 
      i = i + 1; 
      sum += i;
  }
  __VERIFIER_assert( sum == ((SIZE *(SIZE+1))/2));
  return 0;
}
