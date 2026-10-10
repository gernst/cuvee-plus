// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/ps5-ll.c
// SV-COMP nla-digbench/ps5-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/ps5-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int k;
  int y;
  int x;
  int c;
  k = __VERIFIER_nondet_int();
  y = 0;
  x = 0;
  c = 0;
  while (1 != 0) {
    assert(
      6 * y * y * y * y * y + 15 * y * y * y * y + 10 * y * y * y - 30 * x - y
        == 0);
    if (!(c < k)) {
      break;
    }
    c = c + 1;
    y = y + 1;
    x = y * y * y * y + x;
  }
  assert(
    6 * y * y * y * y * y + 15 * y * y * y * y + 10 * y * y * y - 30 * x - y
      == 0);
  assert(k * y == y * y);
  result = 0;
  return result;
}

