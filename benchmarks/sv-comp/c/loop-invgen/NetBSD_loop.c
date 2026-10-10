// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/NetBSD_loop.c
// SV-COMP loop-invgen/NetBSD_loop.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/NetBSD_loop.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int M;
  int p;
  M = __VERIFIER_nondet_int();
  if (!(M > 0)) {
    return;
  }
  p = 0;
  while (p <= M) {
    assert(0 <= p);
    assert(p < M + 1);
    p = p + 1;
  }
}

