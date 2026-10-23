// ./Cuvee.sh examples/c/parsing/declarations.c
// declarations: the builtins of the harness of SV-COMP with pointers in their signatures (see examples/c/harness.c),
// nondeterministic doubles, pointer parameters, unnamed parameters, and typedefs of structs
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
extern double __VERIFIER_nondet_double(void);
int f(int *p);
int g(int, int);
typedef struct { int n; } S;
int main(void) { return g(1, 2); }
