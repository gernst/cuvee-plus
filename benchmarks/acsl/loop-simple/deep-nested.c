// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (the error is reached when all counters are uint32_max-2), the loop invariants only bound the counters
// This file is part of the SV-Benchmarks collection of verification tasks:
// https://github.com/sosy-lab/sv-benchmarks
//
// SPDX-FileCopyrightText: 2019 Philipp Berger, RWTH Aachen University
//
// SPDX-License-Identifier: Apache-2.0

/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "deep-nested.c", 2, "reach_error"); }

int main() {
	unsigned a, b, c, d, e;

	unsigned uint32_max;
	uint32_max = 0xffffffff;

	/*@ loop invariant 0 <= a <= uint32_max-1;
	    loop assigns a, b, c, d, e; */
	for (a = 0; a < uint32_max - 1; ++a) {
		/*@ loop invariant 0 <= b <= uint32_max-1;
		    loop assigns b, c, d, e; */
		for (b = 0; b < uint32_max - 1; ++b) {
			/*@ loop invariant 0 <= c <= uint32_max-1;
			    loop assigns c, d, e; */
			for (c = 0; c < uint32_max - 1; ++c) {
				/*@ loop invariant 0 <= d <= uint32_max-1;
				    loop assigns d, e; */
				for (d = 0; d < uint32_max - 1; ++d) {
					/*@ loop invariant 0 <= e <= uint32_max-1;
					    loop assigns e; */
					for (e = 0; e < uint32_max - 1; ++e) {
						if ((a == b) && (b == c) && (c == d) && (d == e) && (e == (uint32_max - 2))) {
							{reach_error();}
						}
					}
				}
			}
		}
	}

	return 0;
}
