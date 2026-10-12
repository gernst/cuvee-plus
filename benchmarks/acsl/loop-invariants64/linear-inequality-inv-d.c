// ACSL annotations added by hand (benchmarks/acsl/README.md)
// This file is part of the SV-Benchmarks collection of verification tasks:
// https://github.com/sosy-lab/sv-benchmarks
//
// SPDX-FileCopyrightText: 2022 Dirk Beyer, Matthias Dangl, Daniel Dietsch, Matthias Heizmann, Thomas Lemberger, and Michael Tautschnig
//
// SPDX-License-Identifier: Apache-2.0

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "linear-inequality-inv-a.c", 2, "reach_error"); }
/*@ assigns \nothing; */
extern unsigned int __VERIFIER_nondet_uint(void);
int main() {
  unsigned int n = __VERIFIER_nondet_uint();
  if (n == 0) {
    return 0;
  }
  unsigned int   v = 0;
  unsigned long  s = 0;
  unsigned long  i = 0;
  /*@ loop invariant 0 <= i <= n;
      loop invariant s <= 4294967295*i;
      loop invariant v <= s;
      loop assigns i, v, s; */
  while (i < n) {
    v = __VERIFIER_nondet_uint();
    s += v;
    ++i;
  }
  if (s < v) {
    reach_error();
    return 1;
  }
  if (s > 18446744065119617025ULL) { // (2**32 - 1)**2
    reach_error();
    return 1;
  }
  return 0;
}
