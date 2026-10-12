// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/egcd3-ll
/* extended Euclid's algorithm */
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "egcd3-ll.c", 4, "reach_error"); }
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
    long long a, b, p, q, r, s;
    x = __VERIFIER_nondet_int();
    assume_abort_if_not(x>=0 && x<=50);
    y = __VERIFIER_nondet_int();
    assume_abort_if_not(y>=0 && y<=50);
    assume_abort_if_not(x >= 1);
    assume_abort_if_not(y >= 1);

    a = x;
    b = y;
    p = 1;
    q = 0;
    r = 0;
    s = 1;

    /*@ loop invariant a == y*r + x*p;
        loop invariant b == x*q + y*s;
        loop invariant a >= 1;
        loop invariant b >= 0;
        loop assigns a, b, p, q, r, s; */
    while (1) {
        if (!(b != 0))
            break;
        long long c, k;
        c = a;
        k = 0;

        /*@ loop invariant a == y*r + x*p;
            loop invariant b == x*q + y*s;
            loop invariant a == k*b + c;
            loop invariant c >= 0;
            loop invariant b >= 1;
            loop assigns c, k; */
        while (1) {
            if (!(c >= b))
                break;
            long long d, v;
            d = 1;
            v = b;

            /*@ loop invariant a == y*r + x*p;
                loop invariant b == x*q + y*s;
                loop invariant a == k*b + c;
                loop invariant v == b*d;
                loop invariant c >= v;
                loop invariant d >= 1;
                loop invariant b >= 1;
                loop assigns d, v; */
            while (1) {
                __VERIFIER_assert(a == y * r + x * p);
                __VERIFIER_assert(b == x * q + y * s);
                __VERIFIER_assert(a == k * b + c);
                __VERIFIER_assert(v == b * d);

                if (!(c >= 2 * v))
                    break;
                d = 2 * d;
                v = 2 * v;
            }
            c = c - v;
            k = k + d;
        }

        a = b;
        b = c;
        long long temp;
        temp = p;
        p = q;
        q = temp - q * k;
        temp = r;
        r = s;
        s = temp - s * k;
    }
    __VERIFIER_assert(p*x - q*x + r*y - s*y  == a);
    return 0;
}
