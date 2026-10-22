// ./Cuvee.sh -vcgen -z3 examples/c/parsing/safe_allocations.c
// safe_malloc and safe_calloc, with which SV-COMP replaces allocations that are not checked for NULL, are malloc and calloc,
// as are their variants that loop forever on NULL, safe_malloc_or_loop and safe_calloc_or_loop (verifythis/tree_del_iter)
typedef unsigned int size_t;
extern void abort(void);
void *malloc(unsigned int size);
extern void *calloc(size_t num, size_t size);
void *safe_malloc(unsigned int size) {
  void *p = malloc(size);
  if (p == 0) {
    abort();
  }
  return p;
}

void *safe_calloc(size_t num, size_t size) {
  void *p = calloc(num, size);
  if (p == 0) {
    abort();
  }
  return p;
}

void *safe_malloc_or_loop(unsigned int size) {
  void *p = malloc(size);
  if (p == 0) {
    while (1) { }
  }
  return p;
}

void *safe_calloc_or_loop(unsigned int num, unsigned int size) {
  void *p = calloc(num, size);
  if (p == 0) {
    while (1) { }
  }
  return p;
}

int main(void) { int n = 3; int *a = safe_malloc(sizeof(int) * n); a[1] = 2; assert(a[1] == 2); int *c = safe_calloc(n, sizeof(int)); assert(c[2] == 0);
  int *d = safe_malloc_or_loop(sizeof(int) * n); d[0] = 1; assert(d[0] == 1); int *e = safe_calloc_or_loop(n, sizeof(int)); assert(e[1] == 0); return 0; }
