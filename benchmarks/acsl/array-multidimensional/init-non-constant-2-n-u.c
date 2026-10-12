// ACSL annotations added by hand (benchmarks/acsl/README.md): the elements are unsigned, stated modulo 2^32; q and s are signed and may be negative, in which case the loops are not entered
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "init-non-constant-2-n-u.c", 3, "reach_error"); }
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
    ERROR: {reach_error();abort();}
  }
  return;
}
/*@ assigns \nothing; */
int __VERIFIER_nondet_int();
/*@ assigns \nothing; */
unsigned int __VERIFIER_nondet_uint();

int main()
{

	int i,j;
	int m=1000,n=1500;
	int q,s;
	unsigned int A [m][n];
	unsigned int C=__VERIFIER_nondet_uint();
        
        q= __VERIFIER_nondet_int();
        s= __VERIFIER_nondet_int();

	i=0;
	j=0;
	assume_abort_if_not(q<m);
	assume_abort_if_not(s<n);

	/*@ loop invariant 0 <= i && (i <= q || i == 0);
	    loop invariant \forall integer x0, x1; 0 <= x0 < i && 0 <= x1 < s ==> A[x0][x1] == (x0 + x1 + C) % 4294967296;
	    loop assigns i, j, A[0..q-1][0..s-1]; */
	while(i < q){
		j=0;
		/*@ loop invariant 0 <= i < q;
		    loop invariant 0 <= j && (j <= s || j == 0);
		    loop invariant \forall integer x0, x1; 0 <= x0 < i && 0 <= x1 < s ==> A[x0][x1] == (x0 + x1 + C) % 4294967296;
		    loop invariant \forall integer x1; 0 <= x1 < j ==> A[i][x1] == (i + x1 + C) % 4294967296;
		    loop assigns j, A[0..q-1][0..s-1]; */
		while(j < s){
                        A[i][j]=i+j+C;
			j=j+1;
		}
		i=i+1;
    }


	i=0;
	j=0;
	/*@ loop invariant 0 <= i && (i <= q || i == 0);
	    loop invariant \forall integer x0, x1; 0 <= x0 < q && 0 <= x1 < s ==> A[x0][x1] == (x0 + x1 + C) % 4294967296;
	    loop assigns i, j; */
	while(i < q){
		j=0;
		/*@ loop invariant 0 <= i < q;
		    loop invariant 0 <= j && (j <= s || j == 0);
		    loop invariant \forall integer x0, x1; 0 <= x0 < q && 0 <= x1 < s ==> A[x0][x1] == (x0 + x1 + C) % 4294967296;
		    loop assigns j; */
		while(j < s){
                        __VERIFIER_assert(A[i][j]==i+j+C);
			j=j+1;
		}
		i=i+1;
    }

return 0;

}
