// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (y == x after the loop)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "Mono4_1.c", 3, "reach_error"); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

int main() {
    int x = 0;
    int y = 500000;
    /*@ loop invariant x <= 1000000;
        loop invariant x <= 500000 ==> y == 500000;
        loop invariant x >= 500000 ==> y == x;
        loop assigns x, y; */
    while(x < 1000000) {
	if (x < 500000) {
	    x = x + 1;
	} else {
	    x = x + 1;
	    y = y + 1;
	}
    }
    __VERIFIER_assert(y!=x);
    return 0;
}
