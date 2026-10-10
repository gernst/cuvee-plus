// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/apache-escape-absolute.c
// SV-COMP loop-invgen/apache-escape-absolute.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/apache-escape-absolute.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int tmp_4;
  int scheme;
  int urilen;
  int tokenlen;
  int cp;
  int c;
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
  assert(cp - 1 < urilen);
  assert(0 <= cp - 1);
  tmp_1 = __VERIFIER_nondet_int();
  if (tmp_1 != 0) {
    assert(cp < urilen);
    assert(0 <= cp);
    while (cp != urilen - 1) {
      tmp_2 = __VERIFIER_nondet_int();
      if (tmp_2 != 0) {
        break;
      }
      assert(cp < urilen);
      assert(0 <= cp);
      cp = cp + 1;
    }
    assert(cp < urilen);
    assert(0 <= cp);
    if (cp == urilen - 1) {
      result = 0;
      return result;
    }
    assert(cp + 1 < urilen);
    assert(0 <= cp + 1);
    if (cp + 1 == urilen - 1) {
      result = 0;
      return result;
    }
    cp = cp + 1;
    scheme = cp;
    tmp_3 = __VERIFIER_nondet_int();
    if (tmp_3 != 0) {
      c = 0;
      assert(cp < urilen);
      assert(0 <= cp);
      while (cp != urilen - 1 && c < tokenlen - 1) {
        assert(cp < urilen);
        assert(0 <= cp);
        tmp_4 = __VERIFIER_nondet_int();
        if (tmp_4 != 0) {
          c = c + 1;
          assert(c < tokenlen);
          assert(0 <= c);
          assert(cp < urilen);
          assert(0 <= cp);
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

