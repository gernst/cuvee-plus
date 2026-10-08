// ./Cuvee.sh -simplify -chc examples/c/horn/while.c
// expected: valid
// calls in the conditions of loops are evaluated before each iteration, also after continue
extern _Bool __VERIFIER_nondet_bool(void); int main(void) { int i = 0; while (__VERIFIER_nondet_bool()) i++; assert(i >= 0); return 0; }
