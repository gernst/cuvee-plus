// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/sendmail-close-angle.c
// SV-COMP loop-invgen/sendmail-close-angle.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/sendmail-close-angle.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int inp;
  int inlen;
  int bufferlen;
  int buf;
  int buflim;
  int b;
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
    assert(0 <= buf);
    assert(buf < bufferlen);
    buf = buf + 1;
    inp = inp + 1;
    assert(0 <= inp);
    assert(inp < inlen);
    b = __VERIFIER_nondet_int();
  }
  assert(0 <= buf);
  assert(buf < bufferlen);
  buf = buf + 1;
  assert(0 <= buf);
  assert(buf < bufferlen);
  buf = buf + 1;
}

