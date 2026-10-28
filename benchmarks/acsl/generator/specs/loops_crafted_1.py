mono_x = lambda hi, mid: [f'x <= {hi}', f'x >= {mid} ==> x % 2 == 0', 'assigns x']
mono_xy = lambda mid, y0: ['x <= 1000000', f'x <= {mid} ==> y == {y0}', f'x >= {mid} ==> y == x', 'assigns x, y']
mono_z = lambda op: ['x <= 10000000', 'y == 10000000', 'x <= 5000000 ==> z == 5000000', f'x >= 5000000 ==> z == {op}', 'assigns x, z']
sumt = lambda vs: [' + '.join(vs) + ' == l', 'l <= n', 'assigns l, ' + ', '.join(vs)]
inde = {
 'in-de20.c': [['x + y == n', 'assigns x, y'], ['x + z == n', 'assigns x, z']],
 'in-de31.c': [['x + y == n', 'assigns x, y'], ['x + z == n', 'y == n', 'assigns x, z'], ['y + z == n', 'assigns y, z']],
 'in-de32.c': [['x + y == n', 'assigns x, y'], ['x + z == n', 'y == n', 'assigns x, z'], ['x == y', 'assigns x, y']],
 'in-de41.c': [['x + y == n', 'assigns x, y'], ['x + z == n', 'y == n', 'assigns x, z'], ['y + z == n', 'x == n', 'assigns y, z'], ['x + y == n', 'assigns x, y']],
 'in-de42.c': [['x + y == n', 'assigns x, y'], ['x + z == n', 'y == n', 'assigns x, z'], ['y + z == n', 'x == n', 'assigns y, z'], ['x + z == 2*n', 'assigns x, z']],
 'in-de51.c': [['x + y == n', 'assigns x, y'], ['x + z == n', 'y == n', 'assigns x, z'], ['y + z == n', 'x == n', 'assigns y, z'], ['x + y == n', 'z == n', 'assigns x, y'], ['x + z == n', 'assigns x, z']],
 'in-de52.c': [['x + y == n', 'assigns x, y'], ['x + z == n', 'y == n', 'assigns x, z'], ['y + z == n', 'x == n', 'assigns y, z'], ['x + y == n', 'z == n', 'assigns x, y'], ['y == z', 'assigns y, z']],
 'in-de61.c': [['x + y == n', 'assigns x, y'], ['x + z == n', 'y == n', 'assigns x, z'], ['y + z == n', 'x == n', 'assigns y, z'], ['x + y == n', 'z == n', 'assigns x, y'], ['x + z == n', 'y == n', 'assigns x, z'], ['y + z == n', 'assigns y, z']],
 'in-de62.c': [['x + y == n', 'assigns x, y'], ['x + z == n', 'y == n', 'assigns x, z'], ['y + z == n', 'x == n', 'assigns y, z'], ['x + y == n', 'z == n', 'assigns x, y'], ['x + z == n', 'y == n', 'assigns x, z'], ['x == y', 'assigns x, y']],
}
nested3 = [['x <= 0x0fffffff', 'assigns x, y, z'], ['y <= 0x0fffffff', 'assigns y, z'], ['z <= 0x0fffffff', 'assigns z']]
nested5 = lambda vhi: [['w <= 0x0fffffff', 'assigns w, x, y, z, v'], ['x <= 10', 'assigns x, y, z, v'], ['y <= 10', 'assigns y, z, v'], ['z <= 10', 'assigns z, v'], [f'v <= {vhi}', 'assigns v']]
delay_inner = ['0 <= c <= SIZE', '(st == 0) <==> (last < c)', 'assigns c, st']
theatre = {'requires': ['requires 1 <= n <= 109 && 1 <= m <= 109 && 1 <= a <= 109', 'assigns \\nothing', 'ensures \\result == ((n + a - 1) / a) * ((m + a - 1) / a)']}
theatre_loops = [['i >= 0', 'b == i*a', 'i == 0 || (i-1)*a < n', 'assigns b, i'], ['j >= 0', 'l == j*a', 'j == 0 || (j-1)*a < m', 'assigns l, j'], ['0 <= x <= i', 'y == x*j', 'assigns x, y']]
SPECS = {
 'discover_list.c': {'loops': 'skip', 'note': 'a large program with structs and library calls, only the harness is annotated'},
 'iftelse.c': {'loops': [['i % 3 == 0', 'i % 2 == 0 ==> 2*j == i', 'i % 2 == 1 ==> 2*j == i + 3', 'j + k == i', 'i <= n + 2', 'assigns i, j, k']]},
 'loopv1.c': {'loops': [['i % 3 == 0', 'assigns i']]},
 'loopv2.c': {'loops': [['i % 4 == 0', '(i == 0 && j == 0) || j == i + 2', 'assigns i, j'], ['j % 2 == 0', 'k % 2 == 0', 'assigns j, k']], 'note': 'the second loop never terminates (j stays even)'},
 'loopv3.c': {'loops': [['i % 4 == 0', 'assigns i']]},
 'Mono1_1-1.c': {'loops': [mono_x(100000000, 10000000)], 'note': 'expected verdict false (x == 100000000 after the loop)'},
 'Mono1_1-2.c': {'loops': [mono_x(100000000, 10000000)]},
 'Mono3_1.c': {'loops': [['x <= 1000000', 'x <= 500000 ==> y == x', 'x >= 500000 ==> y == 1000000 - x', 'assigns x, y']], 'note': 'expected verdict false (y == 0 after the loop)'},
 'Mono4_1.c': {'loops': [mono_xy(500000, 500000)], 'note': 'expected verdict false (y == x after the loop)'},
 'Mono5_1.c': {'loops': [mono_z('10000000 - x')], 'note': 'expected verdict false (z == 0 after the loop)'},
 'Mono6_1.c': {'loops': [mono_z('x')], 'note': 'expected verdict false (z == x after the loop)'},
 'mono-crafted_10.c': {'loops': [mono_z('x')]},
 'mono-crafted_11.c': {'loops': [mono_x(100000000, 10000000)]},
 'mono-crafted_12.c': {'loops': [['z % 2 == 0', 'assigns x, z']]},
 'mono-crafted_13.c': {'loops': [['x <= 1000000', 'x <= 50000 ==> y == 50000', 'x >= 50000 ==> y == x && x % 2 == 0', 'assigns x, y'], ['x == y', 'z == 0', 'assigns x, y']]},
 'mono-crafted_14.c': {'loops': [mono_xy(500000, 500000), ['z >= 0', 'x == 1000000 - z', 'y == 1000000 - 2*z', 'assigns x, y, z']]},
 'mono-crafted_1.c': {'loops': [mono_xy(50000, 50000), ['x == y', 'z == 0', 'assigns x, y']]},
 'mono-crafted_3.c': {'loops': [mono_xy(500000, 500000), ['z >= 0', 'x == 1000000 - z', 'y == 1000000 - 2*z', 'assigns x, y, z']]},
 'mono-crafted_6.c': {'loops': [['x <= 1000000', 'x >= 750000 ==> x % 2 == 0', 'assigns x, y']]},
 'mono-crafted_7.c': {'loops': [mono_xy(50000, 50000), ['x == y', 'y % 2 == 0', 'z == 0', 'assigns x, y']]},
 'mono-crafted_8.c': {'loops': [mono_z('10000000 - x')]},
 'mono-crafted_9.c': {'loops': [mono_xy(500000, 500000)]},
 'nested3-1_abstracted.c': {'loops': nested3[:2]},
 'nested3-1.c': {'loops': nested3},
 'nested3-2_abstracted.c': {'loops': nested3[:2], 'note': 'expected verdict false (z == 0x0fffffff is not divisible by 4)'},
 'nested3-2.c': {'loops': nested3, 'note': 'expected verdict false (z == 0x0fffffff is not divisible by 4)'},
 'nested5-1.c': {'loops': nested5(10)},
 'nested5-2.c': {'loops': nested5('0x0fffffff'), 'note': 'expected verdict false (v == 0x0fffffff is not divisible by 4)'},
 'nested_delay_nd.c': {'loops': [['a == b', 'd == 0', 'last > 0', 'assigns a, b, c, st, d'], delay_inner + ['a == b', 'd == 0']]},
 'nested_delay_notd2.c': {'loops': [['0 <= d <= SIZE', 'last > 0', 'assigns a, b, c, st, d'], delay_inner], 'note': 'expected verdict false (d reaches SIZE when last >= SIZE), the invariants bound the counters'},
 'net_reset.c': {'loops': [['0 <= i <= 256', 'batch_at <= 256', 'assigns i, __tmpTR__int_1']],
   'funcs': {'net_reset': ['assigns batch_at', 'ensures batch_at == fstTTL - 1'], 'net_send_batch': ['requires 0 <= batch_at <= 256', 'requires fstTTL == 1', 'assigns __tmpTR__int_1'],
             'net_reopen': ['requires fstTTL == 1', 'assigns batch_at, __tmpTR__int_1']}},
 'sum_by_3_abstracted.c': {'loops': [['i <= n', 'j <= n', 'assigns j'], ['i <= n', 'j <= n', 'k <= n', 'assigns k']]},
 'sum_by_3.c': {'loops': [['i <= n', 'assigns i'], ['i <= n', 'j <= n', 'assigns j'], ['i <= n', 'j <= n', 'k <= n', 'assigns k']]},
 'sum_natnum.c': {'loops': [['0 <= i <= SIZE', '2*sum == i*(i+1)', 'assigns i, sum']]},
 'sumt2.c': {'loops': [sumt(['i', 'j'])]}, 'sumt3.c': {'loops': [sumt(['i', 'j', 'k'])]}, 'sumt4.c': {'loops': [sumt(['i', 'j', 'k', 'v4'])]},
 'sumt5.c': {'loops': [sumt(['i', 'j', 'k', 'v4', 'v3'])]}, 'sumt6.c': {'loops': [sumt(['i', 'j', 'k', 'v4', 'v3', 'v2'])]},
 'sumt7.c': {'loops': [sumt(['i', 'j', 'k', 'v1', 'v2', 'v3', 'v4'])]}, 'sumt8.c': {'loops': [sumt(['i', 'j', 'k', 'v1', 'v2', 'v3', 'v4', 'v5'])]},
 'sumt9.c': {'loops': [sumt(['i', 'j', 'k', 'v1', 'v2', 'v3', 'v4', 'v5', 'v6'])]},
 'theatreSquare.c': {'loops': theatre_loops + theatre_loops, 'funcs': {'correct_version': theatre['requires'], 'student_version': theatre['requires']}},
 'vnew1.c': {'loops': [['i % 3 == 0', 'i <= n + 2', 'k == n - i/3', 'assigns i, k'], ['0 <= j <= n/3', 'k == n - (n+2)/3 - j', 'assigns j, k']]},
 'vnew2.c': {'loops': [['i == j && j == k', 'i % 3 == 0', 'i <= n + 2', 'assigns i, j, k']]},
 'watermelon.c': {'loops': [['0 <= i <= w + 1', 'i % 2 == 0', 'assigns i'], ['0 <= i <= w + 1', 'i % 2 == 0', 'assigns i']],
   'funcs': {'correct_version': ['assigns \\nothing', 'ensures \\result == ((w >= 4 && w % 2 == 0) ? 1 : 0)'], 'student_version': ['assigns \\nothing', 'ensures \\result == ((w >= 4 && w % 2 == 0) ? 1 : 0)']},
   'note': 'the contracts assume the globals true == 1 and false == 0, which ACSL cannot name'},
}
SPECS.update({f: {'loops': l} for f, l in inde.items()})
