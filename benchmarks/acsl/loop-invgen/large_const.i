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
int main(int argc, char* argv[]) {
  int c1 = 4000;
  int c2 = 2000;
  int c3 = 10000;
  int n, v;
  int i, k, j;
  n = __VERIFIER_nondet_int();
  if (!(0 <= n && n < 10)) return 0;
  k = 0;
  i = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant k >= 2000*i;
      loop assigns i, v, k; */
  while( i < n ) {
    i++;
    v = __VERIFIER_nondet_int();
    if (!(0 <= v && n < 2)) return 0;
    if( v == 0 )
      k += c1;
    else if( v == 1 )
      k += c2;
    else
      k += c3;
  }
  j = 0;
  /*@ loop invariant 0 <= j <= n;
      loop invariant k >= 2000*(n - j);
      loop assigns j, k; */
  while( j < n ) {
    __VERIFIER_assert(k > 0);
    j++;
    k--;
  }
  return 0;
}
