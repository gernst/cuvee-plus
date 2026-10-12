// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "linear_sea.ch.c", 3, "reach_error"); }
extern void *calloc(unsigned int num, unsigned int size);
void *safe_calloc(unsigned int num, unsigned int size) {
  void *p = calloc(num, size);
  if (p == 0) {
    abort();
  }
  return p;
}


/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
unsigned int __VERIFIER_nondet_uint();
unsigned int  SIZE;
const unsigned int MAX = 100000;
/*@ requires 0 < n && n == SIZE;
    requires \valid_read(a + (0..n-1));
    requires \exists integer t; 0 <= t < n && a[t] == q;
    assigns \nothing;
    ensures \result == 1; */
int linear_search(int *a, int n, int q) {
  unsigned int j=0;
  /*@ loop invariant 0 <= j <= n;
      loop invariant \forall integer t; 0 <= t < j ==> a[t] != q;
      loop assigns j; */
  while (j<n && a[j]!=q) {
  j++;
  }
  if (j<SIZE) return 1;
  else return 0;
}
int main() { 
  SIZE=(__VERIFIER_nondet_uint()/8)+1;

  if (SIZE > 1 && SIZE < MAX) {
    int *a = safe_calloc(SIZE,sizeof(int));
    a[SIZE/2]=3;
    __VERIFIER_assert(linear_search(a,SIZE,3));
  }
}
