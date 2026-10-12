// ACSL annotations added by hand (benchmarks/acsl/README.md): the invariants of nla-digbench/egcd2-ll
/* extended Euclid's algorithm */
/*@ assigns \nothing;
    ensures \false; */
extern void abort(void);
/*@ assigns \nothing;
    ensures \false; */
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
/*@ requires \false;
    assigns \nothing; */
void reach_error() { __assert_fail("0", "egcd2-ll.c", 4, "reach_error"); }
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

int counter = 0;
int main() {
    int x, y;
    long long a, b, p, q, r, s, c, k, xy, yy;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    assume_abort_if_not(x >= 1);
    assume_abort_if_not(y >= 1);

    a = x;
    b = y;
    p = 1;
    q = 0;
    r = 0;
    s = 1;
    c = 0;
    k = 0;
    xy = (long long) x * y;
    yy = (long long) y * y;
    assume_abort_if_not(xy < 2147483647);
    assume_abort_if_not(yy < 2147483647);

    /*@ loop invariant a == y*r + x*p;
        loop invariant b == x*q + y*s;
        loop invariant xy == x*y;
        loop invariant yy == y*y;
        loop invariant a >= 1;
        loop invariant b >= 0;
        loop assigns a, b, p, q, r, s, c, k;
        loop invariant 0 <= counter <= 10 + 1; */
    while (counter++<10) {
        if (!(b != 0))
            break;
        c = a;
        k = 0;

        /*@ loop invariant a == y*r + x*p;
            loop invariant b == x*q + y*s;
            loop invariant a == k*b + c;
            loop invariant xy == x*y;
            loop invariant yy == y*y;
            loop invariant c >= 0;
            loop invariant b >= 1;
            loop assigns c, k;
            loop invariant 0 <= counter <= 10; */
        while (counter++<10) {
            __VERIFIER_assert(a == k * b + c);
            __VERIFIER_assert(a == y*r + x*p);
            __VERIFIER_assert(b == x * q + y * s);
	    __VERIFIER_assert(q*xy + s*yy - q*x - b*y - s*y + b == 0);
            if (!(c >= b))
                break;
            c = c - b;
            k = k + 1;
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
    

    __VERIFIER_assert(q*x + s*y == 0);
    __VERIFIER_assert(p*x + r*y == a);
    return a;
}
