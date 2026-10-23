// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-invgen/MADWiFi-encode_ie_ok.dfy
// SV-COMP loop-invgen/MADWiFi-encode_ie_ok.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks 0<=p; p+1<bufsize_0
//
// findings: the goal p + 1 < bufsize follows from 2 * ielen + p <= bufsize + 2 * n and n < ielen, i.e.
// 2 * n + 2 <= 2 * ielen, which needs coefficients beyond the difference constraints (see TODO.md); a lemma states it,
// whose side conditions bind a and c by matching the premises of the goal; closed (no output)

// p is at least 2 below b if 2 * a + p <= b + 2 * c and c < a, since then 2 * c + 2 <= 2 * a
lemma {:rw} {:teq} lemma_1(a: int, b: int, c: int, p: int)
  requires 2 * a + p <= b + 2 * c && c < a
  ensures (p + 1 < b) <==> true

method main() returns (result: int) {
  var p: int;
  var i: int;
  var leader_len: int;
  var bufsize: int;
  var bufsize_0: int;
  var ielen: int;
  leader_len := *;
  bufsize := *;
  ielen := *;
  if leader_len > 0 {} else {
    return;
  }
  if bufsize > 0 {} else {
    return;
  }
  if ielen > 0 {} else {
    return;
  }
  if bufsize < leader_len {
    return;
  }
  p := 0;
  bufsize_0 := bufsize;
  bufsize := bufsize - leader_len;
  p := p + leader_len;
  if bufsize < 2 * ielen {
    return;
  }
  i := 0;
  while i < ielen && bufsize > 2 {
    assert 0 <= p;
    assert p + 1 < bufsize_0;
    p := p + 2;
    i := i + 1;
  }
}
