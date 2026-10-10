// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/sqrt1-ll.c
// SV-COMP nla-digbench/sqrt1-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/sqrt1-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void assume_abort_if_not(int cond) {
  if (!(cond != 0)) {
    __VERIFIER_assume(false);
  }
}

int main(void) {
  int result;
  int n;
  int a;
  int s;
  int t;
  n = __VERIFIER_nondet_int();
  a = 0;
  s = 1;
  t = 1;
  while (1 != 0) {
    assert(t == 2 * a + 1);
    assert(s == (a + 1) * (a + 1));
    assert(t * t - 4 * s + 2 * t + 1 == 0);
    if (!(s <= n)) {
      break;
    }
    a = a + 1;
    t = t + 2;
    s = s + t;
  }
  assert(t == 2 * a + 1);
  assert(s == (a + 1) * (a + 1));
  assert(t * t - 4 * s + 2 * t + 1 == 0);
  result = 0;
  return result;
}

