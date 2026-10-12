// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (x == 0 after the accelerated loop)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();
/*@ assigns \nothing; */
extern _Bool __VERIFIER_nondet_bool();
/*@ assigns \nothing; */
extern char __VERIFIER_nondet_char();
/*@ assigns \nothing; */
extern double __VERIFIER_nondet_double();
/*@ assigns \nothing; */
extern float __VERIFIER_nondet_float();
/*@ assigns \nothing; */
extern unsigned long __VERIFIER_nondet_ulong();
/*@ assigns \nothing; */
extern unsigned long long __VERIFIER_nondet_ulonglong();
/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint();
extern int __VERIFIER_nondet_int();
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "const_1-2_abstracted.c", 3, "reach_error"); }

/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main(void) {
  unsigned int x = 1;
  unsigned int y = 0;

  // START CONSTANTEXTRAPOLATION
  if (y < (1024)) {
    long long int y__VERIFIER_LA_tmp0;
    y__VERIFIER_LA_tmp0 = y;
    long long int __VERIFIER_LA_iterations0;
    __VERIFIER_LA_iterations0 = (1024 - y__VERIFIER_LA_tmp0) / 1L;
    unsigned int x__VERIFIER_LA_old_tmp0;
    x__VERIFIER_LA_old_tmp0 = x;
    x = (__VERIFIER_LA_iterations0 * 0L) + (x__VERIFIER_LA_old_tmp0 * 0) + 0;
    unsigned int y__VERIFIER_LA_old_tmp0;
    y__VERIFIER_LA_old_tmp0 = y;
    y = (__VERIFIER_LA_iterations0 * 1L) + y__VERIFIER_LA_old_tmp0;
  }
  // END CONSTANTEXTRAPOLATION

  __VERIFIER_assert(x == 1);
}
