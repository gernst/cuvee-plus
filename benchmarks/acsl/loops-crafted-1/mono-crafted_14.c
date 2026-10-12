// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "mono-crafted_14.c", 3, "reach_error"); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

int main(){
	int x=0,y=500000,z=0;
	x=0;
	/*@ loop invariant x <= 1000000;
	    loop invariant x <= 500000 ==> y == 500000;
	    loop invariant x >= 500000 ==> y == x;
	    loop assigns x, y; */
	while(x<1000000){
		if(x<500000)
			x++;
		else{
			x++;
			y++;
		}
	}
	/*@ loop invariant z >= 0;
	    loop invariant y >= 0;
	    loop invariant x == 1000000 - z;
	    loop invariant y == 1000000 - 2*z;
	    loop assigns x, y, z; */
	while(y>0){
		x--;
		z++;
		y=y-2;
	}
	__VERIFIER_assert(z%2==0);
	__VERIFIER_assert(x%2==0);
	return 0;
}
