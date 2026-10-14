// ./Cuvee.sh -print smt2 examples/c/parsing/location.c
// the loops have the attribute :location (line column function) of their keyword, for the locations of witnesses;
// a tab counts as one column, the loop of a for with continue is located at the for

int sum(int n) {
  int s = 0;
  int i = 0;
  while (i < n) { s = s + i; i++; }
  return s;
}

int main() {
  int x = 0;
  do {
    x++;
  } while (x < 10);

  for (int i = 0; i < 10; i++) {
	while (x > 0) x--;
  }

  for (int j = 0; j < 10; j++) {
    if (j == 5) continue;
    x++;
  }

  return sum(x);
}
