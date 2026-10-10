// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/apache-get-tag.c
// SV-COMP loop-invgen/apache-get-tag.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/apache-get-tag.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int tmp_4;
  int tagbuf_len;
  int t;
  tagbuf_len = __VERIFIER_nondet_int();
  if (tagbuf_len >= 1) {} else {
    result = 0;
    return result;
  }
  t = 0;
  tagbuf_len = tagbuf_len - 1;
  while (1 != 0) {
    if (t == tagbuf_len) {
      assert(0 <= t);
      assert(t <= tagbuf_len);
      result = 0;
      return result;
    }
    tmp_1 = __VERIFIER_nondet_int();
    if (tmp_1 != 0) {
      break;
    }
    assert(0 <= t);
    assert(t <= tagbuf_len);
    t = t + 1;
  }
  assert(0 <= t);
  assert(t <= tagbuf_len);
  t = t + 1;
  while (1 != 0) {
    if (t == tagbuf_len) {
      assert(0 <= t);
      assert(t <= tagbuf_len);
      result = 0;
      return result;
    }
    tmp_2 = __VERIFIER_nondet_int();
    if (tmp_2 != 0) {
      tmp_3 = __VERIFIER_nondet_int();
      if (tmp_3 != 0) {
        assert(0 <= t);
        assert(t <= tagbuf_len);
        t = t + 1;
        if (t == tagbuf_len) {
          assert(0 <= t);
          assert(t <= tagbuf_len);
          result = 0;
          return result;
        }
      }
    } else {
      tmp_4 = __VERIFIER_nondet_int();
      if (tmp_4 != 0) {
        break;
      }
    }
    assert(0 <= t);
    assert(t <= tagbuf_len);
    t = t + 1;
  }
  assert(0 <= t);
  assert(t <= tagbuf_len);
  result = 0;
  return result;
}

