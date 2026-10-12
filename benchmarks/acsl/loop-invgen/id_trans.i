// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (j/4 may reach nlen)
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
  int idBitLength, material_length, nlen;
  int j, k;
  nlen = __VERIFIER_nondet_int();
  idBitLength = __VERIFIER_nondet_int();
  material_length = __VERIFIER_nondet_int();
    if (!( nlen == idBitLength / 32 )) return 0;
  /*@ loop invariant 0 <= j;
      loop assigns j; */
  for (j = 0; (j < idBitLength / 8) && (j < material_length); j++) {
    __VERIFIER_assert( 0 <= j);
    __VERIFIER_assert( j < material_length );
    __VERIFIER_assert( 0 <= j/4 );
    __VERIFIER_assert( j/4 < nlen);
  }
  return 0;
}
