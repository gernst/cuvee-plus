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
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "mine-tutorial-ex4.10.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
int main() {
  int v = 1;
  /*@ loop invariant 1 <= v <= 51;
      loop invariant v % 2 == 1;
      loop assigns v; */
  while (v <= 50) {
    __VERIFIER_assert(1 <= v);
    v += 2;
    __VERIFIER_assert(v <= 52);
  }
  __VERIFIER_assert(51 <= v);
  __VERIFIER_assert(v <= 52);
  return 0;
}
