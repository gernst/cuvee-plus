// ./Cuvee.sh -simplify -chc examples/c/horn/pointers.c
// expected: valid
// pointers that are not allocations are values, which are compared and tested but not dereferenced,
// null pointer constants are 0 and its casts to pointer types, global pointers are null initially
int *g; int *id(int *p) { return p; } int isnull(int *p) { if (p == 0) return 1; return 0; } int main(void) { int *q = (void *) 0; void *v = 0; assert(g == 0 && !q && v == (void *) 0); assert(isnull(id(q)) == 1); assert(q == g);  return 0; }
