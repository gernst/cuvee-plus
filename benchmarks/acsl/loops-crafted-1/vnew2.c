// ACSL annotations added by hand (benchmarks/acsl/README.md); the ranges of the unsigned variables that the loops assign are loop invariants
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "vnew2.c", 3, "reach_error"); }
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
int SIZE = 20000001;
/*@ assigns \nothing; */
unsigned int __VERIFIER_nondet_uint();
int main() {
  unsigned int n,i,k,j;
  n = __VERIFIER_nondet_uint();
  if (!(n <= SIZE)) return 0;
  i = j = k = 0;
  /*@ loop invariant i == j && j == k;
      loop invariant i % 3 == 0;
      loop invariant i <= n + 2;
      loop invariant 0 <= i <= 4294967295;
      loop invariant 0 <= k <= 4294967295;
      loop invariant 0 <= j <= 4294967295;
      loop assigns i, j, k; */
  while( i < n ) {
    i = i + 3;
    j = j+3;
    k = k+3;
  }
  if(n>0)
	  __VERIFIER_assert( i==j && j==k && (i%(SIZE+2)) );
  return 0;
}

