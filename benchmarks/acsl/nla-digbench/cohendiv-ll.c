// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*
  Cohen's integer division
  returns x % y
  http://www.cs.upc.edu/~erodri/webpage/polynomial_invariants/cohendiv.htm
*/
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "cohendiv-ll.c", 8, "reach_error"); }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int(void);
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR:
	{reach_error();}
    }
    return;
}

int main() {
    int x, y;
    long long q, r, a, b;

    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();

    assume_abort_if_not(y >= 1);

    q = 0;
    r = x;
    a = 0;
    b = 0;

    /*@ loop invariant b == y*a;
        loop invariant x == q*y + r;
        loop invariant y >= 1;
        loop assigns q, r, a, b; */
    while (1) {
	__VERIFIER_assert(b == y*a);
	__VERIFIER_assert(x == q*y + r);
    
	if (!(r >= y))
	    break;
	a = 1;
	b = y;

	/*@ loop invariant b == y*a;
	    loop invariant x == q*y + r;
	    loop invariant r >= b;
	    loop invariant a >= 1;
	    loop invariant b >= y;
	    loop invariant y >= 1;
	    loop assigns a, b; */
	while (1) {            
	    __VERIFIER_assert(b == y*a);
	    __VERIFIER_assert(x == q*y + r);
	    __VERIFIER_assert(r >= 0);

	    if (!(r >= 2 * b))
		break;
	    
	    __VERIFIER_assert(r >= 2 * y * a);
	    
	    a = 2 * a;
	    b = 2 * b;
	}
	r = r - b;
	q = q + a;
    }
    
    __VERIFIER_assert(x == q*y + r);
    return 0;
}
