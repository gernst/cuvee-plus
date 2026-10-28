S = lambda b: ['0 <= i <= n', f's <= {b}*i', 'v <= s', 'assigns i, v, s']
SPECS = {
 'bin-suffix-5.c': {'loops': [['x % 8 == 5', 'assigns x']]},
 'const.c': {'loops': [['s == 0', 'assigns s']]},
 'eq1.c': {'loops': [['w == x && y == z', 'assigns w, x, y, z']]},
 'eq2.c': {'loops': [['y == z', 'assigns y, z']]},
 'even.c': {'loops': [['x % 2 == 0', 'assigns x']]},
 'mod4.c': {'loops': [['x % 4 == 0', 'assigns x']]},
 'odd.c': {'loops': [['x % 2 == 1', 'assigns x']]},
 'linear-inequality-inv-a.c': {'loops': [S(255)]},
 'linear-inequality-inv-b.c': {'loops': [['0 <= i <= n', 'assigns i, v, s']],
   'note': 'expected verdict false (s is an unsigned char and wraps around), the loop invariant only bounds i'},
 'linear-inequality-inv-c.c': {'loops': [S(65535)]},
}
