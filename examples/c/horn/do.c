// ./Cuvee.sh -chc -prove examples/c/horn/do.c
// expected: valid
extern _Bool __VERIFIER_nondet_bool(void); int main(void) { int i = 0; do i++; while (__VERIFIER_nondet_bool()); assert(i >= 1); return 0; }
