// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/MADWiFi-encode_ie_ok.c
// SV-COMP loop-invgen/MADWiFi-encode_ie_ok.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/MADWiFi-encode_ie_ok.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "MADWiFi-encode_ie_ok.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void assume_abort_if_not(int cond) {
  if (!cond) { abort(); }
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int p = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int leader_len = __VERIFIER_nondet_int();
  int bufsize = __VERIFIER_nondet_int();
  int bufsize_0_ = __VERIFIER_nondet_int();
  int ielen = __VERIFIER_nondet_int();
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
    __VERIFIER_assert(0 <= p);
    __VERIFIER_assert(p + 1 < bufsize_0_);
    p = p + 2;
    i = i + 1;
  }
}

