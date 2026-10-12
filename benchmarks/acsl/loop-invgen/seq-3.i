// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));

/*@ requires \false;
    assigns \nothing; */
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "assert.h", 3, __extension__ __PRETTY_FUNCTION__); })); }
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
  int n0, n1;
  int i0 = 0;
  int k = 0;
  n0 = __VERIFIER_nondet_int();
  n1 = __VERIFIER_nondet_int();
  if (!(-1000000 <= n0 && n0 < 1000000)) return 0;
  if (!(-1000000 <= n1 && n1 < 1000000)) return 0;
  /*@ loop invariant k == i0;
      loop invariant 0 <= i0;
      loop invariant i0 <= n0 || i0 == 0;
      loop assigns i0, k; */
  while( i0 < n0 ) {
    i0++;
    k++;
  }
  int i1 = 0;
  /*@ loop invariant k == i0 + i1;
      loop invariant 0 <= i1;
      loop invariant i1 <= n1 || i1 == 0;
      loop invariant i0 >= n0;
      loop invariant i0 >= 0;
      loop assigns i1, k; */
  while( i1 < n1 ) {
    i1++;
    k++;
  }
  int j1 = 0;
  /*@ loop invariant k == i0 + i1 - j1;
      loop invariant 0 <= j1;
      loop invariant i0 >= n0;
      loop invariant i1 >= n1;
      loop invariant i0 >= 0;
      loop invariant i1 >= 0;
      loop assigns j1, k; */
  while( j1 < n0 + n1 ) {
      __VERIFIER_assert(k > 0);
      j1++;
      k--;
  }
}
