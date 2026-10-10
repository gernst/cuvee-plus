// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/MADWiFi-encode_ie_ok.c
// SV-COMP loop-invgen/MADWiFi-encode_ie_ok.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/MADWiFi-encode_ie_ok.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int p;
  int i;
  int leader_len;
  int bufsize;
  int bufsize_0_;
  int ielen;
  leader_len = __VERIFIER_nondet_int();
  bufsize = __VERIFIER_nondet_int();
  ielen = __VERIFIER_nondet_int();
  if (leader_len > 0) {} else {
    return result;
  }
  if (bufsize > 0) {} else {
    return result;
  }
  if (ielen > 0) {} else {
    return result;
  }
  if (bufsize < leader_len) {
    return result;
  }
  p = 0;
  bufsize_0_ = bufsize;
  bufsize = bufsize - leader_len;
  p = p + leader_len;
  if (bufsize < 2 * ielen) {
    return result;
  }
  i = 0;
  while (i < ielen && bufsize > 2) {
    assert(0 <= p);
    assert(p + 1 < bufsize_0_);
    p = p + 2;
    i = i + 1;
  }
}

