// ACSL annotations added by hand (benchmarks/acsl/README.md): the sums are the logic functions of the axiomatic Asum, the final bound follows from the element-wise property by the lemma total
/*


   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

/* Program Description :-
 * Two arrays are declared of same size.
 * Array1 and Array2 elements are initialized with 0.
 * In while(1) loop, any index is selected non-deterministically.
 * Array1[index] is assigned value count.
 * Array2[index] is assigned -count, if index is not multiple of three. 
 * Sum of both arrays should never exceed one third of array size plus two. 
 * */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array9_pattern.c", 28, "reach_error"); }
extern void abort(void);
/*@ assigns \nothing;
    ensures cond != 0; */
void assume_abort_if_not(int cond) {
  if(!cond) {abort();}
}
/*@ requires cond != 0;
    assigns \nothing; */
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: {reach_error();abort();} } }
/*@ assigns \nothing; */
extern int __VERIFIER_nondet_int() ;
/*@ assigns \nothing; */
extern short __VERIFIER_nondet_short() ;

signed long long ARR_SIZE ;

/*@ axiomatic Asum {
  logic integer asum(int *a, integer n) reads a[0..n-1];
  axiom asum_zero: \forall int *a; asum(a, 0) == 0;
  axiom asum_step: \forall int *a, integer n; n >= 0 ==> asum(a, n+1) == asum(a, n) + a[n];
  logic integer sqsum(int *a, integer n) reads a[0..n-1];
  axiom sqsum_zero: \forall int *a; sqsum(a, 0) == 0;
  axiom sqsum_step: \forall int *a, integer n; n >= 0 ==> sqsum(a, n+1) == sqsum(a, n) + a[n]*a[n];
  lemma total: \forall int *a1, int *a2, integer n; n >= 1 && (\forall integer t; 0 <= t < n ==> (t % 3 != 0 ==> a1[t] + a2[t] == 0) && (t % 3 == 0 ==> (a1[t] == 0 || a1[t] == 1) && a2[t] == 0)) ==> 3*(asum(a1, n) + asum(a2, n)) <= n + 2;
} */
int main()
{
	ARR_SIZE = (signed long long)__VERIFIER_nondet_short() ;
	assume_abort_if_not(ARR_SIZE > 0) ;

	int array1[ARR_SIZE] ;
	int array2[ARR_SIZE] ;
	int count = 0, num = -1;
	signed long long sum = 0 ;
	int temp ;
	short index ;

	/*@ loop invariant 0 <= count <= ARR_SIZE;
	    loop invariant \forall integer t; 0 <= t < count ==> array1[t] == 0 && array2[t] == 0;
	    loop assigns count, array1[0..ARR_SIZE-1], array2[0..ARR_SIZE-1]; */
	for(count=0;count<ARR_SIZE;count++)
	{
		array1[count] = 0 ;
		array2[count] = 0 ;
	}

	count = 1 ;

	/*@ loop invariant \forall integer t; 0 <= t < ARR_SIZE ==> (t % 3 != 0 ==> array1[t] + array2[t] == 0) && (t % 3 == 0 ==> (array1[t] == 0 || array1[t] == 1) && array2[t] == 0);
	    loop assigns index, temp, array1[0..ARR_SIZE-1], array2[0..ARR_SIZE-1]; */
	while(1)
        {
		
		index = __VERIFIER_nondet_short() ;
		assume_abort_if_not(index>=0 && index < ARR_SIZE) ;

		array1[index] = num * (num * count) ;
		array2[index] = (index % 3 == 0) ? array2[index] : (num * count) ;
		

		temp = __VERIFIER_nondet_int() ;
		if(temp == 0) break ;
	}

	/*@ loop invariant 0 <= count <= ARR_SIZE;
	    loop invariant \forall integer t; 0 <= t < ARR_SIZE ==> (t % 3 != 0 ==> array1[t] + array2[t] == 0) && (t % 3 == 0 ==> (array1[t] == 0 || array1[t] == 1) && array2[t] == 0);
	    loop invariant sum == asum(array1, count) + asum(array2, count);
	    loop assigns count, sum; */
	for(count=0;count<ARR_SIZE;count++)
	{
		sum = sum  + array1[count] + array2[count];
	}

	__VERIFIER_assert(3 * sum <= ARR_SIZE+2) ;
	return 0 ;
}

		
