// ./Cuvee.sh -vcgen -z3 examples/c/vcgen/harness.c
// expected: valid
// the harness of SV-COMP as in preprocessed tasks (.i), whose builtins are skipped, and __VERIFIER_assert is an assertion
extern void abort(void);
extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (__const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { ((void) sizeof ((0) ? 1 : 0), __extension__ ({ if (0) ; else __assert_fail ("0", "harness.c", 3, __extension__ __PRETTY_FUNCTION__); })); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}

int main(void) {
  int x = __VERIFIER_nondet_int();
  int y;

  if (x < 0)
    y = -x;
  else
    y = x;

end:
  __VERIFIER_assert(y >= 0);
  return 0;
}
