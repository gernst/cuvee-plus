N = 200000
A = lambda lo, hi, body: f'\\forall integer t; {lo} <= t < {hi} ==> {body}'
cs2 = lambda hi: A('0', hi, 't != z ==> a2[t] == a1[t]')
def pmc(R, T=None, lim=None):
    """partial_mod_count: zeros of a at the multiples of R above T, at most lim of them (k counts them in the first loop)"""
    if lim is None:
        zero = f'(t > {T} && t % {R} == 0)'
        cnt = f'(i >= {T} + 2 ? (i-1)/{R} - ({T})/{R} : 0)'
        k = []
    else:
        T_ = '-1' if T is None else T
        zero = f'(t > {T_} && t % {R} == 0 && (t-1)/{R} - ({T_})/{R} < {lim})'
        cnt = f'\\min({lim}, (i >= {T_} + 2 ? (i-1)/{R} - ({T_})/{R} : 0))'
        k = [f'k == {cnt}']
    content = lambda hi: A('0', hi, f'a[t] == ({zero} ? 0 : t+1)')
    return {'loops': [['0 <= i <= N', content('i')] + k + ['assigns i, k, a[0..N-1]' if k else 'assigns i, a[0..N-1]'],
                      ['0 <= i <= N', content('N'), f'j == {cnt}', 'assigns i, j']],
            'note': 'the zeros of a are the multiples of R above the threshold, counted in closed form with integer division'}
SPECS = {
 'copysome1-1.i': {'loops': [[f'0 <= i <= {N}', f'assigns i, a1[0..{N-1}]'], [f'0 <= i <= {N}', cs2('i'), f'assigns i, a2[0..{N-1}]'], [f'0 <= x <= {N}', cs2(N), 'assigns x']]},
 'copysome1-2.i': {'loops': [[f'0 <= i <= {N}', f'assigns i, a1[0..{N-1}]'], [f'0 <= i <= {N}', cs2('i'), f'assigns i, a2[0..{N-1}]'], [f'0 <= x <= {N}', A('0', N, 't != 150000 ==> a2[t] == a1[t]'), 'assigns x']],
   'note': 'expected verdict false (z is moved to 150001 before the check)'},
 'copysome2-1.i': {'loops': [[f'0 <= i <= {N}', f'assigns i, a1[0..{N-1}]'], [f'0 <= i <= {N}', cs2('i'), f'assigns i, a2[0..{N-1}]'],
   [f'0 <= i <= {N}', cs2(N), A('0', 'i', 'a3[t] == a1[t]'), f'assigns i, a3[0..{N-1}]'], [f'0 <= x <= {N}', A('0', N, 'a3[t] == a1[t]'), 'assigns x']]},
 'copysome2-2.i': {'loops': [[f'0 <= i <= {N}', f'assigns i, a1[0..{N-1}]'], [f'0 <= i <= {N}', cs2('i'), f'assigns i, a2[0..{N-1}]'],
   [f'0 <= i <= {N}', cs2(N), A('0', 'i', 'a3[t] == a1[t]'), f'assigns i, a3[0..{N-1}]'], [f'0 <= x <= {N}', A('0', N, 'a3[t] == a1[t]'), cs2(N), 'assigns x']],
   'note': 'expected verdict false (a2[z] is arbitrary)'},
 'partial_mod_count_limited_base.c': pmc('R', 'N/2', '1'),
 'partial_mod_count_limited_gen.c': pmc('R', 'N/R', 'lim'),
 'partial_mod_count_limited_1.c': pmc('R', None, 'lim'),
}
for r in range(1, 6):
    SPECS[f'partial_mod_count_{r}.c'] = pmc('R', 'N/2')
    if r > 1: SPECS[f'partial_mod_count_limited_{r}.c'] = pmc('R', 'N/2', 'lim')
