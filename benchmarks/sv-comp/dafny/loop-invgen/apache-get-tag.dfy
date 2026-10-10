// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-invgen/apache-get-tag.dfy
// SV-COMP loop-invgen/apache-get-tag.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks 0 <= t; t <= tagbuf_len; 0 <= t; t <= tagbuf_len; 0 <= t;
// t <= tagbuf_len; 0 <= t; t <= tagbuf_len; 0 <= t; t <= tagbuf_len; 0 <= t; t <= tagbuf_len; 0 <= t; t <=
// tagbuf_len; 0 <= t; t <= tagbuf_len

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var tmp₄: int;
  var tagbuf_len: int;
  var t: int;
  tagbuf_len := *;
  if tagbuf_len >= 1 {} else {
    result := 0;
    return;
  }
  t := 0;
  tagbuf_len := tagbuf_len - 1;
  while (1 != 0) {
    if t == tagbuf_len {
      assert 0 <= t;
      assert t <= tagbuf_len;
      result := 0;
      return;
    }
    tmp₁ := *;
    if (tmp₁ != 0) {
      break;
    }
    assert 0 <= t;
    assert t <= tagbuf_len;
    t := t + 1;
  }
  assert 0 <= t;
  assert t <= tagbuf_len;
  t := t + 1;
  while (1 != 0) {
    if t == tagbuf_len {
      assert 0 <= t;
      assert t <= tagbuf_len;
      result := 0;
      return;
    }
    tmp₂ := *;
    if (tmp₂ != 0) {
      tmp₃ := *;
      if (tmp₃ != 0) {
        assert 0 <= t;
        assert t <= tagbuf_len;
        t := t + 1;
        if t == tagbuf_len {
          assert 0 <= t;
          assert t <= tagbuf_len;
          result := 0;
          return;
        }
      }
    } else {
      tmp₄ := *;
      if (tmp₄ != 0) {
        break;
      }
    }
    assert 0 <= t;
    assert t <= tagbuf_len;
    t := t + 1;
  }
  assert 0 <= t;
  assert t <= tagbuf_len;
  result := 0;
  return;
}
