// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "mono-crafted_12.c", 3, "reach_error"); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

int main() {
unsigned int x = 0;
unsigned int y = 10000000;
unsigned int z=0;
	/*@ loop invariant z % 2 == 0;
	    loop assigns x, z; */
	while(x<y){	
		if(x>=5000000)
			z=z+2;
		x++;
	}
  __VERIFIER_assert(!(z%2));
  return 0;
}
