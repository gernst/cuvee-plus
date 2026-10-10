// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/sumt6.c
// SV-COMP loops-crafted-1/sumt6.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/sumt6.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int n;
  int i;
  int k;
  int j;
  int l;
  int v2;
  int v3;
  int v4;
  n = 0;
  i = 0;
  k = 0;
  j = 0;
  l = 0;
  v2 = 0;
  v3 = 0;
  v4 = 0;
  n = __VERIFIER_nondet_int();
  while (l < n) {
    if (!(l % 6 != 0)) {
      v2 = v2 + 1;
    } else if (!(l % 5 != 0)) {
      v3 = v3 + 1;
    } else if (!(l % 4 != 0)) {
      v4 = v4 + 1;
    } else if (!(l % 3 != 0)) {
      i = i + 1;
    } else if (!(l % 2 != 0)) {
      j = j + 1;
    } else {
      k = k + 1;
    }
    l = l + 1;
  }
  assert(i + j + k + v4 + v3 + v2 == l);
  result = 0;
  return result;
}

