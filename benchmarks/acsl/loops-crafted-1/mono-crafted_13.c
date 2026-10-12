// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "mono-crafted_13.c", 3, "reach_error"); }
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }

int main(){
	int x=0,y=50000,z=0;
	x=0;
	/*@ loop invariant x <= 1000000;
	    loop invariant x <= 50000 ==> y == 50000;
	    loop invariant x >= 50000 ==> y == x && x % 2 == 0;
	    loop assigns x, y; */
	while(x<1000000){
		if(x<50000)
			x++;
		else{
			x=x+2;
			y=y+2;
		}
	}
	/*@ loop invariant x == y;
	    loop invariant z == 0;
	    loop assigns x, y; */
	while(y>z){
		y--;
		x--;
	}
	__VERIFIER_assert((x%2==0));
	return 0;
}
