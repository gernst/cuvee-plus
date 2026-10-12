// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (a == 6 after the loop), the loop invariant bounds a
// This file is part of the SV-Benchmarks collection of verification tasks:
// https://github.com/sosy-lab/sv-benchmarks
//
// This file was part of CPAchecker,
// a tool for configurable software verification:
// https://cpachecker.sosy-lab.org
//
// SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
//
// SPDX-License-Identifier: Apache-2.0

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "nested_1b.c", 13, "reach_error"); }

int main() {
	int a = 6;


	/*@ loop invariant 0 <= a <= 6;
	    loop assigns a; */
	for(a = 0; a < 6; ++a) {

	}
	if(a == 6 ) {
		reach_error();
	}
	return 1;
}
