// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/MADWiFi-encode_ie_ok.dfy
// SV-COMP loop-invgen/MADWiFi-encode_ie_ok.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: a program of the folder; checks 0<=p; p+1<bufsize_0

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
  if !(leader_len < 1000000) {
    result := 0;
    return;
  }
  if !(bufsize < 1000000) {
    result := 0;
    return;
  }
  if !(ielen < 1000000) {
    result := 0;
    return;
  }
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
