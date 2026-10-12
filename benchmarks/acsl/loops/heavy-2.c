// ACSL annotations added by hand (benchmarks/acsl/README.md)
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "heavy-2.c", 3, "reach_error"); }

/* Licensed under the GPLv2 */

int main(int argc, char **argv)
{
	static char array[1024 * 1024] = { 1 };
	unsigned int a = 1, i, j, k;

	/*@ loop invariant 0 <= i <= 1048576;
	    loop invariant a == 1;
	    loop assigns i, j, k, array[0..1048575]; */
	for (i = 0; i < sizeof(array); i++)
		/*@ loop invariant 0 <= j <= 1048576;
		    loop invariant a == 1;
		    loop assigns j, k, array[0..1048575]; */
		for (j = 0; j < sizeof(array); j++)
			/*@ loop invariant 0 <= k <= 1048576;
			    loop invariant a == 1;
			    loop assigns k, array[0..1048575]; */
			for (k = 0; k < sizeof(array); k++)
				array[i] = array[j] + array[k];

	if (a != 1)
		goto ERROR;

	return array[100];
ERROR: {reach_error();abort();}
	return 1;
}
