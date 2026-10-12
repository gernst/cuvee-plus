// ACSL annotations added by hand (benchmarks/acsl/README.md): expected verdict false (array1[42] stays 0); the element-wise property that still holds and the sums as logic functions
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
 * Two arrays are declared of same size. All elements are initialized to 0.
 * In while(1) loop, any index is selected non-deterministically.
 * If index is an even number Array1[index] is initialized with count, and
 * Array2[index] is initialized with -count. However, when index is odd,
 * exactly reverse is intialized.
 * Sum of both array should be always zero.
 *
 * Changelog --> 22 November 2019
 * Variable count is reset on reaching 200. One can have any other integer value as well
 * to reset count. It is an additional challenge for Tools/solvers using supervised learning
 * based techniques for algorithm selection. 200 is the max unrolling for most of the reachsafe
 * programs to reach property violation. Presence of 200 as part of statement assignment 
 * inside loop can be picked up by algorithm selector to deploy only falsification/correctness proving
 * techniques.
 * */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array5_pattern.c", 36, "reach_error"); }
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
  logic integer asum(int *a, integer n);
  axiom asum_zero: \forall int *a; asum(a, 0) == 0;
  axiom asum_step: \forall int *a, integer n; n > 0 ==> asum(a, n) == asum(a, n-1) + a[n-1];
  logic integer sqsum(int *a, integer n);
  axiom sqsum_zero: \forall int *a; sqsum(a, 0) == 0;
  axiom sqsum_step: \forall int *a, integer n; n > 0 ==> sqsum(a, n) == sqsum(a, n-1) + a[n-1]*a[n-1];
} */
int main()
{
	ARR_SIZE = (signed long long)__VERIFIER_nondet_short() ;
	assume_abort_if_not(ARR_SIZE > 0) ;

	int array1[ARR_SIZE] ;
	int array2[ARR_SIZE] ;
	int count = 0, num = -1 ;
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

	/*@ loop invariant \forall integer t; 0 <= t < ARR_SIZE ==> t % 2 == 1 ==> array1[t] + array2[t] == 0;
	    loop invariant 1 <= count <= 200;
	    loop assigns index, temp, array1[0..ARR_SIZE-1], array2[0..ARR_SIZE-1], count; */
	while(1)
        {
		
		index = __VERIFIER_nondet_short() ;	
		assume_abort_if_not(index>=0 && index < ARR_SIZE) ;
		

		if(index % 2 == 0){
			if (index == 42) {
				array1[index] = 0 ;
			} else {
				array1[index] = num * (num * count) ;
			}

			array2[index] = num * count ;
		}
		else{
			array1[index] = num * count ;
			array2[index] = num * (num * count) ;
		}

		if(count == 200)
			count = 0 ;	
		count++ ;

		temp = __VERIFIER_nondet_int() ;
		if(temp == 0) break ;
	}

	/*@ loop invariant 0 <= count <= ARR_SIZE;
	    loop invariant \forall integer t; 0 <= t < ARR_SIZE ==> t % 2 == 1 ==> array1[t] + array2[t] == 0;
	    loop invariant sum == asum(array1, count) + asum(array2, count);
	    loop assigns count, sum; */
	for(count=0;count<ARR_SIZE;count++)
	{
		sum = sum  + array1[count] + array2[count];
	}

	__VERIFIER_assert(sum == 0) ;
	return 0 ;
}

		
