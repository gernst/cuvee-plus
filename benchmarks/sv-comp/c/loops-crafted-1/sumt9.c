// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/sumt9.c
// SV-COMP loops-crafted-1/sumt9.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/sumt9.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int n;
  int i;
  int k;
  int j;
  int l;
  int v1;
  int v2;
  int v3;
  int v4;
  int v5;
  int v6;
  n = 0;
  i = 0;
  k = 0;
  j = 0;
  l = 0;
  v1 = 0;
  v2 = 0;
  v3 = 0;
  v4 = 0;
  v5 = 0;
  v6 = 0;
  n = __VERIFIER_nondet_int();
  while (l < n) {
    if (!(l % 9 != 0)) {
      v6 = v6 + 1;
    } else if (!(l % 8 != 0)) {
      v5 = v5 + 1;
    } else if (!(l % 7 != 0)) {
      v1 = v1 + 1;
    } else if (!(l % 6 != 0)) {
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
    assert(i + j + k + v1 + v2 + v3 + v4 + v5 + v6 == l);
  }
  result = 0;
  return result;
}

