A = lambda lo, hi, body: f'\\forall integer t; {lo} <= t < {hi} ==> {body}'
good = 'volArray[t] >= MINVAL || volArray[t] == 0'
CC = 'CELLCOUNT'
def mbpr(k):
    loops = []
    for j in range(k):
        loops.append([f'1 <= i <= {CC}/{k} + 1', f'{CC} % {k} == 0', A('0', CC, f't % {k} < {j} ==> ({good})'), A('0', f'(i-1)*{k}', f't % {k} == {j} ==> ({good})'), f'assigns i, volArray[0..{CC}-1]'])
    loops.append([f'0 <= i <= {CC}', A('0', CC, good), 'assigns i'])
    return {'loops': loops}
def nr(k):
    return {'loops': [[f'1 <= i <= {CC}/{k} + 1', f'{CC} % {k} == 0', A('0', f'(i-1)*{k}', good), f'assigns i, j, volArray[0..{CC}-1]'],
      [f'0 <= j <= {k}', f'1 <= i <= {CC}/{k}', A('0', f'(i-1)*{k}', good), A(f'(i-1)*{k}', f'i*{k} - j', good), f'assigns j, volArray[0..{CC}-1]'],
      [f'0 <= i <= {CC}', A('0', CC, good), 'assigns i']]}
def pnr(k):
    return {'loops': [[f'1 <= i <= SIZE/{k} + 1', f'SIZE % {k} == 0', A('0', f'(i-1)*{k}', 'a[t] != DEFAULTVAL'), 'DEFAULTVAL == 0 && FIXEDVAL == 10', 'assigns i, value, a[0..SIZE-1]'],
      ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] != DEFAULTVAL'), 'assigns i']], 'funcs': {'ReadFromPort': ['assigns \\nothing']}}
def pr(k):
    return {'loops': [[f'1 <= i <= {CC}/{k} + 1', f'{CC} % {k} == 0', A('0', f'(i-1)*{k}', good), f'assigns i, volArray[0..{CC}-1]'], [f'0 <= i <= {CC}', A('0', CC, good), 'assigns i']]}
rev = lambda a, b: f'a[t] == {a}[SIZE-t-1] && b[t] == {b}[SIZE-t-1]'
SPECS = {
 'mlceu2.c': {'loops': [['0 <= i <= SIZE', 'SIZE < 100000', A('0', 'i', 'a[t] == 0'), 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] == 0'), 'assigns i']],
   'note': 'i >> 16 stays 0 or 1 below MAX'},
 'mlceu.c': {'loops': [['0 <= i <= SIZE', A('0', 'i', 'a[t] == (t >> 16 > 250 ? 1 : 0)'), 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] == (t >> 16 > 250 ? 1 : 0)'), 'assigns i']],
   'note': 'expected verdict false (i >> 16 exceeds 250 for large SIZE)'},
 'poly1.c': {'loops': [['0 <= i <= SIZE', A('0', 'i', 'a[t] == t*t'), 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] == t*t'), 'assigns i']]},
 'poly2.c': {'loops': [['0 <= i <= SIZE', A('0', 'i', 'a[t] == t*t + 2'), 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', A('0', 'i', 'a[t] == t*t'), A('i', 'SIZE', 'a[t] == t*t + 2'), 'assigns i, a[0..SIZE-1]'],
   ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] == t*t'), 'assigns i']]},
 'revcpyswp2.c': {'loops': [['0 <= i <= SIZE', 'assigns i, a_copy[0..SIZE-1], b_copy[0..SIZE-1]'],
   ['0 <= i <= SIZE', A('0', 'i', rev('a_copy', 'b_copy')), 'assigns i, a[0..SIZE-1], b[0..SIZE-1]'],
   ['0 <= i <= SIZE', A('0', 'i', rev('b_copy', 'a_copy')), A('i', 'SIZE', rev('a_copy', 'b_copy')), 'assigns i, tmp, a[0..SIZE-1], b[0..SIZE-1]'],
   ['0 <= i <= SIZE', A('0', 'i', rev('a_copy', 'b_copy')), A('i', 'SIZE', rev('b_copy', 'a_copy')), 'assigns i, tmp, a[0..SIZE-1], b[0..SIZE-1]'],
   ['0 <= i <= SIZE', A('0', 'SIZE', rev('a_copy', 'b_copy')), 'assigns i']]},
 'rew.c': {'loops': [['0 <= i <= SIZE', A('0', 'i', 'a[t] == val2'), 'val2 == 3 && low == 2', 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] == val2'), 'val2 == 3 && low == 2', 'assigns i']]},
 'rewnif.c': {'loops': [['0 <= i <= SIZE', A('0', 'i', 'a[t] == t'), 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] == t'), 'assigns i']]},
 'rewnifrev2.c': {'loops': [['-1 <= i <= SIZE-2', f'i == SIZE-2 || ({A("i+1", "SIZE", "a[t] == t")})', 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] == t'), 'assigns i']]},
 'rewnifrev.c': {'loops': [['-1 <= i <= SIZE-1', A('i+1', 'SIZE', 'a[t] == t'), 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] == t'), 'assigns i']]},
 'rewrev.c': {'loops': [['-2 <= i <= SIZE-2', A('i+2', 'SIZE', 'a[t] == val2'), 'val2 == 3 && low == 2', 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] == val2'), 'val2 == 3 && low == 2', 'assigns i']]},
 'skipped.c': {'loops': [['0 <= i <= SIZE', 'assigns i, a[0..SIZE-1]'], ['1 <= i <= SIZE/2 + 1', 'SIZE % 2 == 0', A('0', '2*(i-1)', 'a[t] <= t'), 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', A('0', 'SIZE', 'a[t] <= t'), 'assigns i']]},
 'skippedu.c': {'loops': [['0 <= i <= SIZE', 'assigns i, a[0..SIZE-1]'], ['1 <= i <= SIZE/2 + 1', 'SIZE % 2 == 0', 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE', 'assigns i']],
   'note': 'expected verdict false (the comparison with i leaves elements above their index)'},
 'tcpy.c': {'loops': [['0 <= i <= SIZE', 'assigns i, a[0..SIZE-1]'], ['0 <= i <= SIZE/2', 'SIZE % 2 == 0', A('0', 'i', 'acopy[t] == a[t]'), A('SIZE-i', 'SIZE', 'acopy[t] == a[t]'), 'assigns i, acopy[0..SIZE-1]'],
   ['0 <= i <= SIZE', A('0', 'SIZE', 'acopy[t] == a[t]'), 'assigns i']]},
}
for k in range(2, 6):
    SPECS[f'mbpr{k}.c'] = mbpr(k); SPECS[f'nr{k}.c'] = nr(k); SPECS[f'pnr{k}.c'] = pnr(k); SPECS[f'pr{k}.c'] = pr(k)
