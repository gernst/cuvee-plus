// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/for_bounded_loop1.c
// SV-COMP loops/for_bounded_loop1.yml, translated from benchmarks/sv-comp/dafny/loops/for_bounded_loop1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int i;
  int x;
  int y;
  int n;
  i = 0;
  x = 0;
  y = 0;
  tmp_1 = __VERIFIER_nondet_int();
  n = tmp_1;
  if (!(n > 0)) {
    result = 0;
    return result;
  }
  i = 0;
  while (i < n) {
    x = x - y;
    assert(x == 0);
    y = __VERIFIER_nondet_int();
    if (!(y != 0)) {
      result = 0;
      return result;
    }
    x = x + y;
    assert(x != 0);
    i = i + 1;
  }
  assert(x == 0);
}

