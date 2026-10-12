// ACSL annotations added by hand (benchmarks/acsl/README.md): the equality is stated modulo 2^64 since x and y are unsigned long long, by the logic function g2 with the trusted lemma g2_step: the polynomial of the next iteration is z times that of this one
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
void reach_error() { __assert_fail("0", "geo2-ll.c", 8, "reach_error"); }
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


/*@ axiomatic Geo2 {
  logic integer g2(integer x, integer y, integer z);
  axiom g2_def: \forall integer x, y, z; g2(x, y, z) == (1 + x*z - x - z*y) % 18446744073709551616;
  lemma g2_step: \forall integer x, y, z; g2(x, y, z) == 0 ==>
    g2((unsigned long long)((unsigned long long)(x * (unsigned long long) z) + 1), (unsigned long long)(y * (unsigned long long) z), z) == 0;
} */
int main() {
    int z, k;
    unsigned long long x, y, c;
    z = __VERIFIER_nondet_int();
    k = __VERIFIER_nondet_int();

    x = 1;
    y = 1;
    c = 1;

    /*@ loop invariant g2(x, y, z) == 0;

        loop invariant 0 <= x <= 18446744073709551615 && 0 <= y <= 18446744073709551615;
        loop invariant c >= 1;
        loop assigns x, y, c; */
    while (1) {
        __VERIFIER_assert(1 + x*z - x - z*y == 0);

        if (!(c < k))
            break;

        c = c + 1;
        x = x * z + 1;
        y = y * z;
    }
    __VERIFIER_assert(1 + x*z - x - z*y == 0);
    return 0;
}
