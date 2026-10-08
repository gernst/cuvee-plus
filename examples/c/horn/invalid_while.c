// ./Cuvee.sh -simplify -chc examples/c/horn/invalid_while.c
// expected: invalid
extern _Bool __VERIFIER_nondet_bool(void); int main(void) { int i = 0; while (__VERIFIER_nondet_bool()) i++; assert(i == 0); return 0; }
