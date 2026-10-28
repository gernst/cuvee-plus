import os, re
ACSL = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))  # benchmarks/acsl
D = os.path.join(ACSL, 'array-fpi')
B = '0 <= i <= N'; B1 = '1 <= i <= N'
C = lambda a, e: f'\\forall integer t; 0 <= t < i ==> {a}[t] == {e}'       # the prefix written so far
R = lambda a, e: f'\\forall integer t; i <= t < N ==> {a}[t] == {e}'       # the rest, still old
ALL = lambda a, e: f'\\forall integer t; 0 <= t < N ==> {a}[t] == {e}'
W = lambda *xs: 'assigns i, ' + ', '.join(xs)
A_ = lambda a: f'{a}[0..N-1]'
S = 'sum[0]'
def fam(name):
    k = int(re.search(r'\d', name).group(0)) if re.search(r'\d', name) else None
    base = re.sub(r'\d', '', name)
    if base == 'brs':
        return [[B, C('a', f'(t % {k} == 0 ? {k} : 0)'), W(A_('a'))], [B, ALL('a', f'(t % {k} == 0 ? {k} : 0)'), f'i >= 1 ==> 0 <= {S} <= {k}*(i-1)', W(S)]]
    if base == 'ms':
        return [[B, C('a', f't % {k}'), W(A_('a'))], [B, ALL('a', f't % {k}'), f'i >= 1 ==> 0 <= {S} <= {k-1}*(i-1)', W(S)]]
    if name == 'conda':
        return [[B, C('a', '1'), W(A_('a'))], [B, C('a', '2'), R('a', '1'), W(A_('a'))], [B, ALL('a', '2'), f'{S} == 2*i', W(S)]]
    if name == 'condg':
        return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('a', '0'), R('a', '1'), W(A_('a'))], [B, ALL('a', '0'), W()]]
    if name == 'condm':
        return [[B, C('a', '0'), W(A_('a'))], [B, C('a', '(N % 2 == 0 ? 2 : 1)'), R('a', '0'), W(A_('a'))], [B, ALL('a', '(N % 2 == 0 ? 2 : 1)'), W()]]
    if name == 'condn':
        return [[B, W(A_('a'))], [B, '\\forall integer t; 0 <= t < i ==> a[t] <= N', W(A_('a'))], [B, '\\forall integer t; 0 <= t < N ==> a[t] <= N', W()]]
    if base in ('eqn', 'ifeqn'):
        b0 = B1 if base == 'eqn' else B
        return [[b0, C('a', f'{2*k}*(t+1)'), W(A_('a'))], [b0, ALL('a', f'{2*k}*(t+1)'), C('b', f'{k}*t*t + {k}*t + 1'), W(A_('b'))], [B, ALL('b', f'{k}*t*t + {k}*t + 1'), W()]]
    if name in ('ifcomp', 'pcomp', 'ifncomp', 'ncomp'):
        b0 = B if name.startswith('if') else B1; c0 = 'N + ' if 'ncomp' in name else ''
        return [[b0, C('a', '6*(t+1)'), W(A_('a'))], [b0, ALL('a', '6*(t+1)'), C('b', '3*t*t + 3*t + 1'), W(A_('b'))],
                [b0, ALL('b', '3*t*t + 3*t + 1'), C('c', f'{c0}t*t*t'), W(A_('c'))], [B, ALL('c', f'{c0}t*t*t'), W()]]
    if base == 'indp':
        steps = {2: ['(t-1)*(t+1)', '-1', '0'], 3: ['(t-1)*(t-1)', 't*t - t + 1', 't*t + 1', 't*t'], 4: ['(t+1)*(t+1)', 't*t + t + 1', 't*t + 1'], 5: ['(t+1)*(t+1)', '2*t + 1', 't + 1', '1']}[k]
        loops = []
        for j, e in enumerate(steps):
            inv = [B, C('a', e)] + ([R('a', steps[j-1])] if j > 0 else []) + [W(A_('a'))]
            loops.append(inv)
        if k == 5: loops.append([B, ALL('a', '1'), f'{S} == i', W(S)])
        else: loops.append([B, ALL('a', steps[-1]), W()])
        return loops
    if name == 'modn':
        return [[B, f'{S} == i', W(S)], [B, f'{S} == N', C('a', '0'), W(A_('a'))], [B, ALL('a', '0'), W()]]
    if name == 'modp':
        return [[B, f'{S} == i', W(S)], [B, f'{S} == N', C('a', 'N'), W(A_('a'))], [B, ALL('a', 'N'), W()]]
    if name == 'mods':
        return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('a', 'N + 1'), R('a', '1'), W(A_('a'))],
                [B, f'{S} == N', C('a', '0'), R('a', 'N + 1'), W(A_('a'))], [B, ALL('a', '0'), W()]]
    if name in ('nsqm', 'nsqm-if', 'sqm', 'sqm-if'):
        b0 = B if name.endswith('if') else B1; n0 = 'N + ' if name.startswith('n') else ''
        return [[b0, C('b', '2*t + 1'), W(A_('b'))], [b0, ALL('b', '2*t + 1'), C('a', f'{n0}(t+1)*(t+1)'), W(A_('a'))], [B, ALL('a', f'{n0}(t+1)*(t+1)'), W()]]
    if name == 'res1':
        return [[B, C('a', '1'), W(A_('a'))], [B, C('b', '1'), W(A_('b'))], [B, ALL('a', '1'), ALL('b', '1'), f'{S} == i', W(S)], [B, ALL('b', '1'), f'{S} == N + i', W(S)]]
    if name == 'res1o':
        return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('b', '1'), W(A_('b'))], [B, ALL('b', '1'), f'{S} == N + i', W(S)]]
    if name == 'res2':
        return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('b', '1'), W(A_('b'))], [B, ALL('b', '1'), f'{S} == N + i', W(S)],
                [B, f'{S} == 2*N', C('c', '1'), W(A_('c'))], [B, ALL('c', '1'), f'{S} == 2*N + i', W(S)]]
    if name == 'res2o':
        return [[B, C('a', '1'), W(A_('a'))], [B, C('b', '1'), W(A_('b'))], [B, C('c', '1'), W(A_('c'))], [B, ALL('a', '1'), ALL('b', '1'), ALL('c', '1'), f'{S} == i', W(S)],
                [B, ALL('b', '1'), ALL('c', '1'), f'{S} == N + i', W(S)], [B, ALL('c', '1'), f'{S} == 2*N + i', W(S)]]
    m = re.match(r's(\d)(2?)(l?)if$', name)
    if m:
        k = int(m.group(1))
        if not m.group(2) and not m.group(3):   # s{k}if: a == k, sum of a
            return [[B, C('a', str(k)), W(A_('a'))], [B, ALL('a', str(k)), f'{S} == {k}*i', W(S)]]
        return [[B, C('a', '1'), W(A_('a'))], [B, C('a', str(1 + k)), R('a', '1'), W(A_('a'))], [B, ALL('a', str(1 + k)), f'{S} == {1 + k}*i', W(S)]]
    if base == 'sina':
        if k == 1: return [[B, f'{S} == i', W(S)], [B, f'{S} == N', C('a', 'N'), W(A_('a'))], [B, ALL('a', 'N'), W()]]
        if k == 2: return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('a', 'N + 1'), R('a', '1'), W(A_('a'))], [B, ALL('a', 'N + 1'), W()]]
        if k == 3: return [[B, C('a', '1'), W(A_('a'))], [B, C('b', '1'), W(A_('b'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', ALL('b', '1'), C('a', 'N + 1'), W(A_('a'))], [B, ALL('a', 'N + 1'), W()]]
        if k == 4: return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('a', 'N + 1'), R('a', '1'), W(A_('a'))], [B, ALL('a', 'N + 1'), C('b', 'N + 2'), W(A_('b'))], [B, ALL('b', 'N + 2'), W()]]
        if k == 5: return [[B, C('a', '1'), W(A_('a'))], [B, C('b', '1'), W(A_('b'))], [B, ALL('a', '1'), ALL('b', '1'), f'{S} == i', W(S)], [B, ALL('a', '1'), ALL('b', '1'), f'{S} == N + i', W(S)],
                           [B, f'{S} == 2*N', C('a', '2*N + 1'), R('a', '1'), W(A_('a'))], [B, ALL('a', '2*N + 1'), W()]]
    if base == 'ss':
        if k == 1: return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('a', 'N + 1'), R('a', '1'), W(A_('a'))], [B, ALL('a', 'N + 1'), f'{S} == N + (N+1)*i', W(S)]]
        if k == 2: return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('a', '0'), W(A_('a'))], [B, f'{S} == N', C('a', 'N'), R('a', '0'), W(A_('a'))],
                           [B, ALL('a', 'N'), f'{S} == N + N*i', W(S)], [B, f'{S} == N*(N+1)', C('a', 'N*(N+2)'), R('a', 'N'), W(A_('a'))], [B, ALL('a', 'N*(N+2)'), W()]]
        if k == 3: return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('a', '0'), W(A_('a'))], [B, f'{S} == N', C('a', 'N'), R('a', '0'), W(A_('a'))],
                           [B, ALL('a', 'N'), f'{S} == N + N*i', W(S)]]
        if k == 4: return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('a', 'N + 1'), R('a', '1'), W(A_('a'))], [B, ALL('a', 'N + 1'), f'{S} == (N+1)*i', W(S)]]
    if name == 'ssina':
        return [[B, C('a', '1'), W(A_('a'))], [B, ALL('a', '1'), f'{S} == i', W(S)], [B, f'{S} == N', C('a', 'N + 1'), R('a', '1'), W(A_('a'))],
                [B, ALL('a', 'N + 1'), f'{S} == (N+1)*i', W(S)], [B, f'{S} == N*(N+1)', C('a', '(N+1)*(N+1)'), R('a', 'N + 1'), W(A_('a'))], [B, ALL('a', '(N+1)*(N+1)'), W()]]
    raise KeyError(name)

def bounds_only(loops):
    return [[c for c in l if c == B or c == B1 or c.startswith('assigns')] for l in loops]

SPECS = {}
for f in sorted(os.listdir(D)):
    if not f.endswith('.c'): continue
    name = f[:-2]
    false = name.endswith('f') and not name.endswith('if')
    true_name = name[:-1] if false else name
    if true_name == 'indp1': true_name = 'indp4'   # indp1 exists only as a false task, with the loops of indp4
    loops = fam(true_name)
    if false:
        SPECS[f] = {'loops': bounds_only(loops), 'note': f'expected verdict false (a variant of {true_name}), the loops carry bounds only'}
    else:
        SPECS[f] = {'loops': loops}
