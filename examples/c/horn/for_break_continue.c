// ./Cuvee.sh -simplify -chc examples/c/horn/for_break_continue.c
// expected: valid
// continue of a for executes its step, also next to a break, and that of the innermost for only: each iteration
// starts with the counter one step further, which a skipped or a repeated step would violate
int main(void) {
  int i;
  int j;
  int k = 0;
  for (i = 0; i < 10; i++) {
    assert(k == i);
    k++;
    if (i == 7) break;
    int m = 0;
    for (j = 0; j < 3; j++) {
      assert(m == j);
      m++;
      if (j == 1) continue;
    }
    assert(m == 3 && j == 3 && k == i + 1);
    if (i % 2 == 0) continue;
  }
  assert(i == 7);
  return 0;
}
