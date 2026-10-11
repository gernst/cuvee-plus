// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/sendmail-close-angle.c
// SV-COMP loop-invgen/sendmail-close-angle.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/sendmail-close-angle.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sendmail-close-angle.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

void main(void) {
  int inp = __VERIFIER_nondet_int();
  int inlen = __VERIFIER_nondet_int();
  int bufferlen = __VERIFIER_nondet_int();
  int buf = __VERIFIER_nondet_int();
  int buflim = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  inlen = __VERIFIER_nondet_int();
  bufferlen = __VERIFIER_nondet_int();
  if (!(bufferlen > 1 && inlen > 0 && bufferlen < inlen)) {
    return;
  }
  buf = 0;
  inp = 0;
  buflim = bufferlen - 2;
  b = __VERIFIER_nondet_int();
  while (b != 0) {
    if (buf == buflim) {
      break;
    }
    __VERIFIER_assert(0 <= buf);
    __VERIFIER_assert(buf < bufferlen);
    buf = buf + 1;
    inp = inp + 1;
    __VERIFIER_assert(0 <= inp);
    __VERIFIER_assert(inp < inlen);
    b = __VERIFIER_nondet_int();
  }
  __VERIFIER_assert(0 <= buf);
  __VERIFIER_assert(buf < bufferlen);
  buf = buf + 1;
  __VERIFIER_assert(0 <= buf);
  __VERIFIER_assert(buf < bufferlen);
  buf = buf + 1;
}

