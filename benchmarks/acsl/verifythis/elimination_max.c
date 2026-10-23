// This file is part of the SV-Benchmarks collection of verification tasks:
// https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks
//
// SPDX-FileCopyrightText: 2019 Gidon Ernst <gidonernst@gmail.com>
//
// SPDX-License-Identifier: Apache-2.0

extern void *calloc(unsigned int nmemb, unsigned int size);
extern void free(void *);
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "elimination_max.c", 5, "reach_error"); }
extern void abort(void);
void *safe_calloc(unsigned int num, unsigned int size) {
  void *p = calloc(num, size);
  if (p == 0) {
    abort();
  }
  return p;
}

void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
void __VERIFIER_assert(int cond) {
    if(!cond) {reach_error();abort();}
}

extern int __VERIFIER_nondet_int(void);

int main() {
    int n = __VERIFIER_nondet_int();
    /* 1 << 30 will make sure n * sizeof(int) does not overflow */
    assume_abort_if_not(n >= 0 && n < (1 << 30));
    int *a = safe_calloc(n, sizeof(int));

    int x = 0;
    int y = n - 1;

    while(x < y) {
        /* Possible formulation of the invariant:
         *
         * Claude Marche, Jean-Christophe Filliatre
         * forall i. (0 <= i || y < i < n)  ==>  (a[i] <= a[x] && a[i] <= a[y])
         *
         * Gerhard Schellhorn, Bogdan Tofan, Gidon Ernst
         * exists k. x <= k && k < y && k < n && a[k] = max(a, n)
         *      (where max a builtin logic function)
         */
        if(a[x] <= a[y]) x++;
        else y--;
    }

    int i;

    i = __VERIFIER_nondet_int();
    assume_abort_if_not(0 <= i && i < n);
    __VERIFIER_assert(a[i] <= a[x]);

    for(i=0; i<n; i++) {
        __VERIFIER_assert(a[i] <= a[x]);
    }
    free(a);

    return x;
}
