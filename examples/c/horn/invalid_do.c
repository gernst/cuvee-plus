// ./Cuvee.sh -simplify -chc examples/c/horn/invalid_do.c
// expected: invalid
extern _Bool __VERIFIER_nondet_bool(void); int main(void) { int i = 0; do i++; while (__VERIFIER_nondet_bool()); assert(i == 1); return 0; }
