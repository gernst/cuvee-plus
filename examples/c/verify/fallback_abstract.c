// ./Cuvee.sh -unbounded -teq -prove -split -prove -fallback -z3 -verify examples/c/verify/fallback_abstract.c
// the goal of -teq remains, z3 refutes its lowering by -fallback (see teq/fallback_negated.c), which is :abstract,
// i.e., stronger than the goal, hence no counterexample (the assertion does fail)
int main(void) { unsigned int x = 0; unsigned int N; while (x < N) { x += 2; } assert(x % 2); return 0; }
