// ./Cuvee.sh -print dfy examples/c/parsing/modifies.c
// the inferred modifies attributes, also of calls, printed in Dafny
int g; int h; void f(void) { g = 1; } void k(void) { int h; h = 2; f(); } void m(void) { k(); }
