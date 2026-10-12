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
 * Array1[index] is assigned value index.
 * Array2[index] is assigned -index, except index is not the last index. 
 * Sum of both arrays should either be zero or 2 times (size of array - 1) ... 
 * */

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "array11_pattern.c", 28, "reach_error"); }
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
  lemma total: \forall int *a1, int *a2, integer n; n >= 1 && (\forall integer t; 0 <= t < n ==> (t != n-1 ==> a1[t] + a2[t] == 0) && (t == n-1 ==> a1[t] == a2[t] && (a1[t] == 0 || a1[t] == t))) ==> asum(a1, n) + asum(a2, n) == 0 || asum(a1, n) + asum(a2, n) + 2 == 2*n;
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
	signed long long index ;

	/*@ loop invariant 0 <= count <= ARR_SIZE;
	    loop invariant \forall integer t; 0 <= t < count ==> array1[t] == 0 && array2[t] == 0;
	    loop assigns count, array1[0..ARR_SIZE-1], array2[0..ARR_SIZE-1]; */
	for(count=0;count<ARR_SIZE;count++)
	{
		array1[count] = 0 ;
		array2[count] = 0 ;
	}

	/*@ loop invariant \forall integer t; 0 <= t < ARR_SIZE ==> (t != ARR_SIZE-1 ==> array1[t] + array2[t] == 0) && (t == ARR_SIZE-1 ==> array1[t] == array2[t] && (array1[t] == 0 || array1[t] == t));
	    loop assigns index, temp, array1[0..ARR_SIZE-1], array2[0..ARR_SIZE-1]; */
	while(1)
        {
		
		index = (signed long long)__VERIFIER_nondet_short() ;
		assume_abort_if_not(index>=0 && index < ARR_SIZE) ;

		array1[index] = num * (num * (num * (num *index))) ;
		array2[index] = (index == ARR_SIZE-1) ? index : (num * index) ;
		

		temp = __VERIFIER_nondet_int() ;
		if(temp == 0) break ;
	}

	/*@ loop invariant 0 <= count <= ARR_SIZE;
	    loop invariant \forall integer t; 0 <= t < ARR_SIZE ==> (t != ARR_SIZE-1 ==> array1[t] + array2[t] == 0) && (t == ARR_SIZE-1 ==> array1[t] == array2[t] && (array1[t] == 0 || array1[t] == t));
	    loop invariant sum == asum(array1, count) + asum(array2, count);
	    loop assigns count, sum; */
	for(count=0;count<ARR_SIZE;count++)
	{
		sum = sum  + array1[count] + array2[count];
	}

	__VERIFIER_assert(sum == 0 || (sum+2 == 2 * ARR_SIZE)) ;
	return 0 ;
}

		
