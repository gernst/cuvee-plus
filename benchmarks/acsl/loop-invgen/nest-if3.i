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
  int i,k,n,l;
  n = __VERIFIER_nondet_int();
  l = __VERIFIER_nondet_int();
  if (!(l>0)) return 0;
  if (!(l < 1000000)) return 0;
  if (!(n < 1000000)) return 0;
  /*@ loop invariant 1 <= k;
      loop invariant k <= n || k == 1;
      loop invariant l >= 1;
      loop assigns k, i, l; */
  for (k=1;k<n;k++){
    /*@ loop invariant l <= i;
        loop invariant i <= n || i == l;
        loop invariant l >= 1;
        loop assigns i; */
    for (i=l;i<n;i++){
      __VERIFIER_assert(1<=i);
    }
    if(__VERIFIER_nondet_int())
      l = l + 1;
  }
 }
