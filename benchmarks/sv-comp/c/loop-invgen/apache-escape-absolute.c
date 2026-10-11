// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/apache-escape-absolute.c
// SV-COMP loop-invgen/apache-escape-absolute.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/apache-escape-absolute.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "apache-escape-absolute.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  int tmp_4 = __VERIFIER_nondet_int();
  int scheme = __VERIFIER_nondet_int();
  int urilen = __VERIFIER_nondet_int();
  int tokenlen = __VERIFIER_nondet_int();
  int cp = __VERIFIER_nondet_int();
  int c = __VERIFIER_nondet_int();
  urilen = __VERIFIER_nondet_int();
  tokenlen = __VERIFIER_nondet_int();
  scheme = __VERIFIER_nondet_int();
  if (urilen > 0) {} else {
    result = 0;
    return result;
  }
  if (tokenlen > 0) {} else {
    result = 0;
    return result;
  }
  if (scheme >= 0) {} else {
    result = 0;
    return result;
  }
  if (scheme == 0 || urilen - 1 < scheme) {
    result = 0;
    return result;
  }
  cp = scheme;
  __VERIFIER_assert(cp - 1 < urilen);
  __VERIFIER_assert(0 <= cp - 1);
  tmp_1 = __VERIFIER_nondet_int();
  if (tmp_1 != 0) {
    __VERIFIER_assert(cp < urilen);
    __VERIFIER_assert(0 <= cp);
    while (cp != urilen - 1) {
      tmp_2 = __VERIFIER_nondet_int();
      if (tmp_2 != 0) {
        break;
      }
      __VERIFIER_assert(cp < urilen);
      __VERIFIER_assert(0 <= cp);
      cp = cp + 1;
    }
    __VERIFIER_assert(cp < urilen);
    __VERIFIER_assert(0 <= cp);
    if (cp == urilen - 1) {
      result = 0;
      return result;
    }
    __VERIFIER_assert(cp + 1 < urilen);
    __VERIFIER_assert(0 <= cp + 1);
    if (cp + 1 == urilen - 1) {
      result = 0;
      return result;
    }
    cp = cp + 1;
    scheme = cp;
    tmp_3 = __VERIFIER_nondet_int();
    if (tmp_3 != 0) {
      c = 0;
      __VERIFIER_assert(cp < urilen);
      __VERIFIER_assert(0 <= cp);
      while (cp != urilen - 1 && c < tokenlen - 1) {
        __VERIFIER_assert(cp < urilen);
        __VERIFIER_assert(0 <= cp);
        tmp_4 = __VERIFIER_nondet_int();
        if (tmp_4 != 0) {
          c = c + 1;
          __VERIFIER_assert(c < tokenlen);
          __VERIFIER_assert(0 <= c);
          __VERIFIER_assert(cp < urilen);
          __VERIFIER_assert(0 <= cp);
        }
        cp = cp + 1;
      }
      result = 0;
      return result;
    }
  }
  result = 0;
  return result;
}

