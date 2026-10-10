// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/c/loop-invariants/linear-inequality-inv-c.c
// SV-COMP loop-invariants/linear-inequality-inv-c.yml, translated from benchmarks/sv-comp/dafny/loop-invariants/linear-inequality-inv-c.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int M;
  int n;
  int v;
  int s;
  int i;
  n = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= M);
  __VERIFIER_assume(0 <= n && n <= M);
  v = 0;
  s = 0;
  i = 0;
  while (i < n) {
    v = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= v && v <= M);
    s = s + v;
    i = i + 1;
  }
  assert(s >= v);
  assert(s <= M * M);
}

