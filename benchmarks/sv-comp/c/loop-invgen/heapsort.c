// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-invgen/heapsort.c
// SV-COMP loop-invgen/heapsort.yml, translated from benchmarks/sv-comp/dafny/loop-invgen/heapsort.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int n;
  int l;
  int r;
  int i;
  int j;
  n = __VERIFIER_nondet_int();
  if (!(1 <= n)) {
    result = 0;
    return result;
  }
  l = n / 2 + 1;
  r = n;
  if (l > 1) {
    l = l - 1;
  } else {
    r = r - 1;
  }
  while (r > 1) {
    i = l;
    j = 2 * l;
    while (j <= r) {
      if (j < r) {
        assert(1 <= j);
        assert(j <= n);
        assert(1 <= j + 1);
        assert(j + 1 <= n);
        tmp_1 = __VERIFIER_nondet_int();
        if (tmp_1 != 0) {
          j = j + 1;
        }
      }
      assert(1 <= j);
      assert(j <= n);
      tmp_2 = __VERIFIER_nondet_int();
      if (tmp_2 != 0) {
        break;
      }
      assert(1 <= i);
      assert(i <= n);
      assert(1 <= j);
      assert(j <= n);
      i = j;
      j = 2 * j;
    }
    if (l > 1) {
      assert(1 <= l);
      assert(l <= n);
      l = l - 1;
    } else {
      assert(1 <= r);
      assert(r <= n);
      r = r - 1;
    }
  }
  result = 0;
  return result;
}

