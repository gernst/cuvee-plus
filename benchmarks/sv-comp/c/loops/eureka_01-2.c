// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/eureka_01-2.c
// SV-COMP loops/eureka_01-2.yml, translated from benchmarks/sv-comp/dafny/loops/eureka_01-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "eureka_01-2.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void assume_abort_if_not(int cond) {
  if (!cond) { abort(); }
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int INFINITY = __VERIFIER_nondet_int();
  int nodecount = __VERIFIER_nondet_int();
  int edgecount = __VERIFIER_nondet_int();
  int source = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  INFINITY = 899;
  nodecount = 5;
  edgecount = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < edgecount);
  source = 0;
  i = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && edgecount <= N && nodecount <= N && N <= 134217727);
  int Source[N];
  int Dest[N];
  int Weight[N];
  int distance[N];
  while (i < edgecount) {
    tmp_1 = __VERIFIER_nondet_int();
    assume_abort_if_not(0 <= tmp_1 && tmp_1 < nodecount);
    Source[i] = tmp_1;
    tmp_2 = __VERIFIER_nondet_int();
    assume_abort_if_not(0 <= tmp_2 && tmp_2 < nodecount);
    Dest[i] = tmp_2;
    tmp_3 = __VERIFIER_nondet_int();
    assume_abort_if_not(0 <= tmp_3 && tmp_3 <= 1073741823);
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
    __VERIFIER_assert(distance[i] >= 0);
    i = i + 1;
  }
  result = 0;
  return result;
}

