// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops-crafted-1/theatreSquare.c
// SV-COMP loops-crafted-1/theatreSquare.yml, translated from benchmarks/sv-comp/dafny/loops-crafted-1/theatreSquare.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int correct_version(int n, int m, int a) {
  int result;
  int i;
  int j;
  int b;
  int l;
  int x;
  int y;
  i = 0;
  j = 0;
  b = 0;
  l = 0;
  while (b < n) {
    b = b + a;
    i = i + 1;
  }
  while (l < m) {
    l = l + a;
    j = j + 1;
  }
  x = 0;
  y = 0;
  while (x < i) {
    y = y + j;
    x = x + 1;
  }
  result = y;
  return result;
}

int student_version(int n, int m, int a) {
  int result;
  int i;
  int j;
  int b;
  int l;
  int x;
  int y;
  i = 0;
  j = 0;
  b = 0;
  l = 0;
  while (b < n) {
    b = b + a;
    i = i + 1;
  }
  while (l < m) {
    l = l + a;
    j = j + 1;
  }
  x = 0;
  y = 0;
  while (x < i) {
    y = y + j;
    x = x + 1;
  }
  result = y;
  return result;
}

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int tmp_4;
  int a;
  int n;
  int m;
  int n_stones1;
  int n_stones2;
  tmp_1 = __VERIFIER_nondet_int();
  a = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  n = tmp_2;
  tmp_3 = __VERIFIER_nondet_int();
  m = tmp_3;
  tmp_4 = __VERIFIER_nondet_int();
  n_stones2 = tmp_4;
  n_stones1 = n_stones2;
  if (1 <= n && 1 <= m && 1 <= a && n <= 109 && m <= 109 && a <= 109) {
    n_stones1 = correct_version(n, m, a);
    n_stones2 = student_version(n, m, a);
  }
  assert(n_stones1 == n_stones2);
  result = 0;
  return result;
}

