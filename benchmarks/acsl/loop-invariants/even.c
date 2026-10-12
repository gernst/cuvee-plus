// ACSL annotations added by hand (benchmarks/acsl/README.md)
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
void reach_error() { __assert_fail("0", "even.c", 3, "reach_error"); }
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
int main(void) {
  unsigned int x = 0;
  /*@ loop invariant x % 2 == 0;
      loop assigns x; */
  while (__VERIFIER_nondet_int()) {
    x += 2;
  }
  __VERIFIER_assert(!(x % 2));
  return 0;
}
