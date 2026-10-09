// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/apache-escape-absolute.dfy
// SV-COMP loop-invgen/apache-escape-absolute.yml (expected: safe), translated from the C program
// by ./Cuvee.sh -print dfy: a program of the folder; checks cp-1 < urilen; 0 <= cp-1; cp < urilen; 0 <= cp; cp <
// urilen; 0 <= cp; cp < urilen; 0 <= cp; cp+1 < urilen; 0 <= cp+1; cp < urilen; 0<=cp; cp < urilen; 0<=cp; c <
// tokenlen; 0<=c; cp < urilen; 0<=cp

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var tmp₃: int;
  var tmp₄: int;
  var scheme: int;
  var urilen: int;
  var tokenlen: int;
  var cp: int;
  var c: int;
  urilen := *;
  tokenlen := *;
  scheme := *;
  if !(urilen <= 1000000 && urilen >= -1000000) {
    result := 0;
    return;
  }
  if !(tokenlen <= 1000000 && tokenlen >= -1000000) {
    result := 0;
    return;
  }
  if !(scheme <= 1000000 && scheme >= -1000000) {
    result := 0;
    return;
  }
  if urilen > 0 {} else {
    result := 0;
    return;
  }
  if tokenlen > 0 {} else {
    result := 0;
    return;
  }
  if scheme >= 0 {} else {
    result := 0;
    return;
  }
  if scheme == 0 || urilen - 1 < scheme {
    result := 0;
    return;
  }
  cp := scheme;
  assert cp - 1 < urilen;
  assert 0 <= cp - 1;
  tmp₁ := *;
  if (tmp₁ != 0) {
    assert cp < urilen;
    assert 0 <= cp;
    while cp != urilen - 1 {
      tmp₂ := *;
      if (tmp₂ != 0) {
        break;
      }
      assert cp < urilen;
      assert 0 <= cp;
      cp := cp + 1;
    }
    assert cp < urilen;
    assert 0 <= cp;
    if cp == urilen - 1 {
      result := 0;
      return;
    }
    assert cp + 1 < urilen;
    assert 0 <= cp + 1;
    if cp + 1 == urilen - 1 {
      result := 0;
      return;
    }
    cp := cp + 1;
    scheme := cp;
    tmp₃ := *;
    if (tmp₃ != 0) {
      c := 0;
      assert cp < urilen;
      assert 0 <= cp;
      while cp != urilen - 1 && c < tokenlen - 1 {
        assert cp < urilen;
        assert 0 <= cp;
        tmp₄ := *;
        if (tmp₄ != 0) {
          c := c + 1;
          assert c < tokenlen;
          assert 0 <= c;
          assert cp < urilen;
          assert 0 <= cp;
        }
        cp := cp + 1;
      }
      result := 0;
      return;
    }
  }
  result := 0;
  return;
}
