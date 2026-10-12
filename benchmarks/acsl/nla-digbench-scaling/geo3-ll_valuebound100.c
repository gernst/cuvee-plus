// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/geo3-ll; the equality is stated modulo 2^64 since x and y are unsigned long long, by the logic function g3 with the trusted lemma g3_step: the polynomial of the next iteration is z times that of this one; g3_init: it is 0 modulo 2^64 initially
/*
Geometric Series
computes x = sum(z^k)[k=0..k-1], y = z^(k-1)
*/

/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "geo3-ll.c", 8, "reach_error"); }
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
/*@ axiomatic Geo3 {
  logic integer g3(integer x, integer y, integer z, integer a, integer az);
  axiom g3_def: \forall integer x, y, z, a, az; g3(x, y, z, a, az) == (z*x - x + a - az*y) % 18446744073709551616;
  lemma g3_init: \forall integer x, z, a, az; x == (unsigned long long) a && az == a*z ==> g3(x, 1, z, a, az) == 0;
  lemma g3_step: \forall integer x, y, z, a, az; az == a*z && g3(x, y, z, a, az) == 0 ==>
    g3((unsigned long long)((unsigned long long)(x * (unsigned long long) z) + (unsigned long long) a), (unsigned long long)(y * (unsigned long long) z), z, a, az) == 0;
  lemma g3_value: \forall integer x, y, z, a, az; g3(x, y, z, a, az) == 0 ==>
    (unsigned long long)((unsigned long long)((unsigned long long)((unsigned long long)((unsigned long long) z * x) - x)
      + (unsigned long long) a) - (unsigned long long)(az * y)) == 0;
} */
int main() {
    int z, a, k;
    unsigned long long x, y, c, az;
    z = __VERIFIER_nondet_int();
    assume_abort_if_not(z>=0 && z<=100);
    a = __VERIFIER_nondet_int();
    assume_abort_if_not(a>=0 && a<=100);
    k = __VERIFIER_nondet_int();
    assume_abort_if_not(k>=0 && k<=100);

    x = a;
    y = 1;
    c = 1;
    az = (long long) a * z;

    /*@ loop invariant g3(x, y, z, a, az) == 0;

        loop invariant 0 <= x <= 18446744073709551615 && 0 <= y <= 18446744073709551615;
        loop invariant az == a*z;
        loop invariant c >= 1;
        loop assigns x, y, c; */
    while (1) {
        __VERIFIER_assert(z*x - x + a - az*y == 0);

        if (!(c < k))
            break;

        c = c + 1;
        x = x * z + a;
        y = y * z;
    }
    __VERIFIER_assert(z*x - x + a - az*y == 0);
    return x;
}
