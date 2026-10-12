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
int main(){
  int i,pvlen ;
  int tmp___1 ;
  int k = 0;
  int n;
  i = 0;
  pvlen = __VERIFIER_nondet_int();
  /*@ loop invariant 0 <= i <= 1000001;
      loop assigns i; */
  while ( __VERIFIER_nondet_int() && i <= 1000000) {
    i = i + 1;
  }
  if (i > pvlen) {
    pvlen = i;
  }
  i = 0;
  /*@ loop invariant k == i;
      loop invariant 0 <= i <= 1000001;
      loop assigns i, k, tmp___1; */
  while ( __VERIFIER_nondet_int() && i <= 1000000) {
    tmp___1 = i;
    i = i + 1;
    k = k + 1;
  }
  int j = 0;
  n = i;
  /*@ loop invariant k == i;
      loop invariant i + j == n;
      loop invariant 0 <= j <= n;
      loop assigns i, j, k; */
  while (1) {
    __VERIFIER_assert(k >= 0);
    k = k -1;
    i = i - 1;
    j = j + 1;
    if (j >= n) {
      break;
    }
  }
  return 0;
}
