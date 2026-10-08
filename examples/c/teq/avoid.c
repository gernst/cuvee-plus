// ./Cuvee.sh -teq -split -simplify examples/c/teq/avoid.c
// the loop for (i = 0; i != N; i++) runs N times, from the lemma on counters that avoid a value
int main(void) { int i; for (i = 0; i != 100; i++) { assert(i <= 100); } assert(i == 100); return 0; }
