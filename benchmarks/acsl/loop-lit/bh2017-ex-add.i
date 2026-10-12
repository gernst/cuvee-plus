// ACSL annotations added by hand (benchmarks/acsl/README.md)

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

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ requires \false;
    assigns \nothing; */
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "bh-ex-add.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern _Bool __VERIFIER_nondet_bool();
int main() {
  int m = 0;
  int n = 0;
  /*@ loop invariant 0 <= m <= 60;
      loop invariant 0 <= n <= 60;
      loop assigns m, n; */
  while (1) {
    __VERIFIER_assert(m <= 60);
    __VERIFIER_assert(n <= 60);
    if (__VERIFIER_nondet_bool()) {
      if (__VERIFIER_nondet_bool()) {
        if (m < 60) {
          m++;
        }
        else {
          __VERIFIER_assert(m == 60);
          m = 0;
        }
      }
    }
    if (__VERIFIER_nondet_bool()) {
      if (__VERIFIER_nondet_bool()) {
        if (n < 60) {
          n++;
        }
        else {
          __VERIFIER_assert(n == 60);
          n = 0;
        }
      }
    }
  }
  return 0;
}
