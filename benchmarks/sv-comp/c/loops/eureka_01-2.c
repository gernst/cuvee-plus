// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/eureka_01-2.c
// SV-COMP loops/eureka_01-2.yml, translated from benchmarks/sv-comp/dafny/loops/eureka_01-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int INFINITY;
  int nodecount;
  int edgecount;
  int source;
  int Source[];
  int Dest[];
  int Weight[];
  int distance[];
  int x;
  int y;
  int i;
  int j;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  INFINITY = 899;
  nodecount = 5;
  edgecount = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < edgecount);
  source = 0;
  i = 0;
  while (i < edgecount) {
    tmp_1 = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= tmp_1 && tmp_1 < nodecount);
    Source[i] = tmp_1;
    tmp_2 = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= tmp_2 && tmp_2 < nodecount);
    Dest[i] = tmp_2;
    tmp_3 = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= tmp_3);
    Weight[i] = tmp_3;
    i = i + 1;
  }
  i = 0;
  while (i < nodecount) {
    if (i == source) {
      distance[i] = 0;
    } else {
      distance[i] = INFINITY;
    }
    i = i + 1;
  }
  i = 0;
  while (i < nodecount) {
    j = 0;
    while (j < edgecount) {
      x = Dest[j];
      y = Source[j];
      if (distance[x] > distance[y] + Weight[j]) {
        distance[x] = distance[y] + Weight[j];
      }
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  while (i < edgecount) {
    x = Dest[i];
    y = Source[i];
    if (distance[x] > distance[y] + Weight[i]) {
      result = 0;
      return result;
    }
    i = i + 1;
  }
  i = 0;
  while (i < nodecount) {
    assert(distance[i] >= 0);
    i = i + 1;
  }
  result = 0;
  return result;
}

