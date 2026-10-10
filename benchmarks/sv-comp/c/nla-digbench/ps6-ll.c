// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/nla-digbench/ps6-ll.c
// SV-COMP nla-digbench/ps6-ll.yml, translated from benchmarks/sv-comp/dafny/nla-digbench/ps6-ll.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

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
      -2 * y * y * y * y * y * y - 6 * y * y * y * y * y - 5 * y * y * y * y
        + y * y
        + 12 * x
        == 0);
    if (!(c < k)) {
      break;
    }
    c = c + 1;
    y = y + 1;
    x = y * y * y * y * y + x;
  }
  assert(
    -2 * y * y * y * y * y * y - 6 * y * y * y * y * y - 5 * y * y * y * y
      + y * y
      + 12 * x
      == 0);
  assert(k * y == y * y);
  result = 0;
  return result;
}

