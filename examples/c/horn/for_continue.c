// ./Cuvee.sh -simplify -chc examples/c/horn/for_continue.c
// expected: valid
extern _Bool __VERIFIER_nondet_bool(void); int main(void) { int i; int j = 0; for (i = 0; __VERIFIER_nondet_bool(); i++) { if (i > 2) continue; j++; } assert(j <= 3 && j <= i); return 0; }
