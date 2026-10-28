M32 = 4294967296; M64 = 18446744073709551616
mod = lambda e, m: f'({e}) % {m} == 0'
pow2 = lambda v, base='1': f'\\exists integer k; 0 <= k <= 64 && {v} == {base} * (1 << k)'
egcd_ab = ['a == y*r + x*p', 'b == x*q + y*s']
fermat = ['4*(A + r) == u*u - v*v - 2*u + 2*v', 'assigns u, v, r']
lcm1 = [mod('x*u + y*v - a*b', M32), 'x >= 1 && y >= 1', 'assigns x, y, u, v']
dijk = [mod('p*p + r*q - n*q', M32), 'r < 2*p + q', mod('h*h*h - 12*h*n*q + 16*n*p*q - h*q*q - 4*p*q*q + 12*h*q*r - 16*p*q*r', M32),
        mod('h*h*n - 4*h*n*p + 4*(n*n)*q - n*q*q - h*h*r + 4*h*p*r - 8*n*q*r + q*q*r + 4*q*r*r', M32),
        mod('h*h*p - 4*h*n*q + 4*n*p*q - p*q*q + 4*h*q*r - 4*p*q*r', M32), 'q >= 1', pow2('q', '1') , 'q % 4 == 0 || q == 1', 'assigns p, q, r, h']
ps = lambda poly: [poly, 'y == c', '0 <= c', 'c <= k || c == 0', 'assigns c, y, x']
SPECS = {
 'bresenham-ll.c': {'loops': [['2*Y*x - 2*X*y - X + 2*Y - v == 0', '0 <= y <= x', 'x <= X + 1 || x == 0', 'assigns x, y, v, xy, yx']]},
 'cohencu-ll.c': {'loops': [['z == 6*n + 6', 'y == 3*n*n + 3*n + 1', 'x == n*n*n', 'n >= 0', 'n <= a + 1 || n == 0', 'assigns n, x, y, z']]},
 'cohendiv-ll.c': {'loops': [['b == y*a', 'x == q*y + r', 'y >= 1', 'assigns q, r, a, b'], ['b == y*a', 'x == q*y + r', 'r >= b', 'a >= 1', 'b >= y', 'y >= 1', 'assigns a, b']]},
 'dijkstra-u.c': {'loops': [['p == 0 && r == n && h == 0', 'q >= 1', pow2('q', '1'), 'q % 4 == 0 || q == 1', 'assigns q'], dijk],
   'note': 'q is a power of 4, written with a shift; the equalities are stated modulo 2^32 since the variables are unsigned'},
 'divbin2.i': {'loops': [['q == 0 && r == A', 'b >= B', pow2('b', 'B'), 'assigns b'], ['A == q*b + r', 'r < b', 'b >= B', pow2('b', 'B'), 'assigns q, r, b']],
   'note': 'b is B times a power of 2, written with a shift'},
 'divbin.i': {'loops': [['q == 0 && r == A', 'b >= B', pow2('b', 'B'), 'assigns b'], ['A == q*b + r', 'r < b', 'b >= B', pow2('b', 'B'), 'assigns q, r, b']],
   'note': 'expected verdict false (b = 2*b overflows), the invariants are those of divbin2'},
 'egcd2-ll.c': {'loops': [egcd_ab + ['xy == x*y', 'yy == y*y', 'a >= 1', 'b >= 0', 'assigns a, b, p, q, r, s, c, k'], egcd_ab + ['a == k*b + c', 'xy == x*y', 'yy == y*y', 'c >= 0', 'b >= 1', 'assigns c, k']]},
 'egcd3-ll.c': {'loops': [egcd_ab + ['a >= 1', 'b >= 0', 'assigns a, b, p, q, r, s'], egcd_ab + ['a == k*b + c', 'c >= 0', 'b >= 1', 'assigns c, k'],
   egcd_ab + ['a == k*b + c', 'v == b*d', 'c >= v', 'd >= 1', 'b >= 1', 'assigns d, v']]},
 'egcd-ll.c': {'loops': [['p*s - r*q == 1'] + egcd_ab + ['a >= 1 && b >= 1', 'assigns a, b, p, q, r, s']]},
 'fermat1-ll.c': {'loops': [fermat, fermat, fermat]}, 'fermat2-ll.c': {'loops': [fermat]},
 'geo1-ll.c': {'loops': [[mod('x*z - x - y + 1', M64), 'c >= 1', 'assigns x, y, c']], 'note': 'the equality is stated modulo 2^64 since x and y are unsigned long long'},
 'geo1-u.c': {'loops': [[mod('x*z - x - y + 1', M64), 'c >= 1', 'assigns x, y, c']], 'note': 'expected verdict false (z == 0 makes the final step wrap around), the equality is stated modulo 2^64'},
 'geo2-ll.c': {'loops': [[mod('1 + x*z - x - z*y', M64), 'c >= 1', 'assigns x, y, c']], 'note': 'the equality is stated modulo 2^64 since x and y are unsigned long long'},
 'geo3-ll.c': {'loops': [[mod('z*x - x + a - az*y', M64), 'az == a*z', 'c >= 1', 'assigns x, y, c']], 'note': 'the equality is stated modulo 2^64 since x and y are unsigned long long'},
 'hard-ll.c': {'loops': [['q == 0 && r == A', 'd == B*p', 'p >= 1', pow2('p'), 'assigns d, p'], ['A == q*B + r', 'd == B*p', 'r < d', 'r >= 0', 'p >= 1', pow2('p'), 'assigns r, d, p, q']],
   'note': 'p is a power of 2, written with a shift'},
 'hard-u.c': {'loops': [['q == 0 && r == A', mod('d - B*p', M32), 'p >= 1', 'assigns d, p'], [mod('A - q*B - r', M32), mod('d - B*p', M32), 'p >= 1', 'assigns r, d, p, q']],
   'note': 'expected verdict false (d = 2*d overflows), the equalities are stated modulo 2^32'},
 'knuth.i': {'loops': [[mod('d*d*q - 2*q*d - 4*r*d + 4*k*d + 8*r - 8*n', M32), mod('k*t - t*t', M32), mod('d*d*q - 2*d*q - 4*d*r + 4*d*t + 4*a*k - 4*a*t - 8*n + 8*r', M32),
   mod('d*k - d*t - a*k + a*t', M32), 'assigns r, k, q, d, t']], 'note': 'the asserted equalities modulo 2^32 (unsigned variables); sqrt is a floating point call'},
 'lcm1.c': {'loops': [lcm1, lcm1, lcm1], 'note': 'the equality is stated modulo 2^32 since the variables are unsigned'},
 'lcm2.c': {'loops': [[mod('x*u + y*v - 2*a*b', M32), 'x >= 1 && y >= 1', 'assigns x, y, u, v']], 'note': 'the equality is stated modulo 2^32 since the variables are unsigned'},
 'mannadiv.c': {'loops': [['y1*x2 + y2 + y3 == x1', 'y3 >= 0', 'assigns y1, y2, y3']]},
 'prod4br-ll.c': {'loops': [['q + a*b*p == x*y', 'b >= 0', 'assigns a, b, p, q']]},
 'prodbin-ll.c': {'loops': [['z + x*y == a*b', 'y >= 0', 'assigns x, y, z']]},
 'ps2-ll.c': {'loops': [ps('y*y - 2*x + y == 0')]}, 'ps3-ll.c': {'loops': [ps('6*x - 2*y*y*y - 3*y*y - y == 0')]},
 'ps4-ll.c': {'loops': [ps('4*x - y*y*y*y - 2*y*y*y - y*y == 0')]},
 'ps5-ll.c': {'loops': [ps('6*y*y*y*y*y + 15*y*y*y*y + 10*y*y*y - 30*x - y == 0')]},
 'ps6-ll.c': {'loops': [ps('-2*y*y*y*y*y*y - 6*y*y*y*y*y - 5*y*y*y*y + y*y + 12*x == 0')]},
 'sqrt1-ll.c': {'loops': [['t == 2*a + 1', 's == (a + 1)*(a + 1)', 'a >= 0', 'assigns a, s, t']]},
}
