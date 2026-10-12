// ACSL annotations added by hand (benchmarks/acsl/README.md): j is an int compared with the unsigned n, hence 0 <= j; the ranges of the unsigned variables that the loops assign are loop invariants
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "sum_by_3.c", 3, "reach_error"); }
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
  unsigned int n,i,k;
  n = __VERIFIER_nondet_uint();
  if (!(n <= SIZE)) return 0;
  i = 0;
  /*@ loop invariant i <= n;
      loop invariant 0 <= i <= 4294967295;
      loop assigns i; */
  while( i < n ) {
    i = i + 1;
  }
  int j = i;
  /*@ loop invariant i <= n;
      loop invariant 0 <= j <= n;
      loop assigns j; */
  while( j < n ) {
    j = j+1;
  }
  k = j;
  /*@ loop invariant i <= n;
      loop invariant 0 <= j <= n;
      loop invariant k <= n;
      loop invariant 0 <= k <= 4294967295;
      loop assigns k; */
  while( k < n ) {
    k = k+1;
  }
  __VERIFIER_assert((i+j+k)/3 <= SIZE);
  return 0;
}

