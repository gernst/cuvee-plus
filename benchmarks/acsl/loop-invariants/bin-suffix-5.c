// ACSL annotations added by hand (benchmarks/acsl/README.md): & is uninterpreted in Cuvée, the lemma and_5 states the bits of x that the invariant fixes
// This file is part of the SV-Benchmarks collection of verification tasks:
// https://github.com/sosy-lab/sv-benchmarks
//
// SPDX-FileCopyrightText: 2019 Dirk Beyer and Matthias Dangl
//
// SPDX-License-Identifier: Apache-2.0

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "bin-suffix-5.c", 3, "reach_error"); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int();
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ lemma and_5: \forall integer x; 0 <= x && x % 8 == 5 ==> (x & 5) == 5; */
int main(void) {
  unsigned int x = 5;
  /*@ loop invariant x % 8 == 5;
      loop assigns x; */
  while (__VERIFIER_nondet_int()) {
    x += 8;
  }
  __VERIFIER_assert((x & 5) == 5);
  return 0;
}
