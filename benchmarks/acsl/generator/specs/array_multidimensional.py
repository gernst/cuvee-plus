# nested loops over d-dimensional arrays: a phase is d nested loops with the same body; the invariants describe the
# region completed in row-major order
V = ['i', 'j', 'k', 'l']; X = ['x0', 'x1', 'x2', 'x3']
def region(L, bounds, P, lo=None):
    """the completed region when the loop at level L is at its head: tuples lexicographically below (i, j, ..)"""
    d = len(bounds); lo = lo or ['0'] * d
    facts = []
    for l in range(L + 1):
        xs = X[l:d]
        rng = ' && '.join([f'{lo[l]} <= {X[l]} < {V[l]}'] + [f'{lo[t]} <= {X[t]} < {bounds[t]}' for t in range(l + 1, d)])
        idx = V[:l] + xs
        facts.append(f'\\forall integer {", ".join(xs)}; {rng} ==> {P(idx)}')
    return facts
def phase(bounds, P, assigns, lo=None, carry=()):
    d = len(bounds); lo = lo or ['0'] * d
    loops = []
    for L in range(d):
        inv = [f'{lo[t]} <= {V[t]} < {bounds[t]}' for t in range(L)] + [f'{lo[L]} <= {V[L]} <= {bounds[L]}'] + list(carry)
        if P: inv += region(L, bounds, P, lo)
        inv.append('assigns ' + ', '.join(V[L:d] + list(assigns)))
        loops.append(inv)
    return loops
def done(bounds, P, lo=None):
    d = len(bounds); lo = lo or ['0'] * d
    xs = X[:d]
    rng = ' && '.join(f'{lo[t]} <= {X[t]} < {bounds[t]}' for t in range(d))
    return f'\\forall integer {", ".join(xs)}; {rng} ==> {P(xs)}'
def check(bounds, P, lo=None):
    return phase(bounds, None, [], lo, carry=[done(bounds, P, lo)])
el = lambda a, idx: a + ''.join(f'[{x}]' for x in idx)
def arr_assigns(a, bounds): return a + ''.join(f'[0..{b}-1]' for b in bounds)

def standard(bounds, P, out, ins, nondet_init=True, lo=None):
    loops = []
    if nondet_init: loops += phase(bounds, None, [arr_assigns(a, bounds) for a in ins])
    loops += phase(bounds, P, [arr_assigns(out, bounds)], lo)
    loops += check(bounds, P, lo)
    return {'loops': loops}

mn = ['m', 'n']; mnp = ['m', 'n', 'p']; nn = ['n', 'n']; nnn = ['n', 'n', 'n']
addP = lambda idx: f'{el("C", idx)} == {el("A", idx)} + {el("B", idx)}'
copyP = lambda idx: f'{el("A", idx)} == {el("B", idx)}'
SPECS = {
 'add-2-n-u.c': standard(mn, addP, 'C', ['A', 'B']),
 'add-3-n-u.c': standard(mnp, addP, 'C', ['A', 'B']),
 'copy-2-u.c': standard(nn, copyP, 'A', ['B']),
 'copy-3-n-u.c': standard(mnp, copyP, 'A', ['B']),
 'copy-partial-2-n-u.c': {'loops': phase(mn, None, [arr_assigns('B', mn)]) + phase(['q', 's'], copyP, [arr_assigns('A', mn)]) + check(['q', 's'], copyP)},
 'diff-2-n-u.c': {'loops': phase(mn, None, [arr_assigns('A', mn)]) + phase(mn, None, [arr_assigns('B', mn)]) + phase(mn, lambda idx: f'{el("C", idx)} == {el("A", idx)} - {el("B", idx)}', [arr_assigns('C', mn)])
   + check(mn, lambda idx: f'{el("C", idx)} == {el("A", idx)} - {el("B", idx)}'), 'note': 'the elements are unsigned, the difference wraps around in C and in the assertion alike'},
 'diff-3-n-u.c': standard(mnp, addP, 'C', ['A', 'B']),
 'init-2-n-u.c': standard(mn, lambda idx: f'{el("A", idx)} == C', 'A', [], nondet_init=False),
 'init-3-u.c': standard(nnn, lambda idx: f'{el("A", idx)} == C', 'A', [], nondet_init=False),
 'init-4-n-u.c': standard(['m', 'n', 'p', 'q'], lambda idx: f'{el("A", idx)} == C', 'A', [], nondet_init=False),
 'init-non-constant-2-n-u.c': standard(['q', 's'], lambda idx: f'{el("A", idx)} == {idx[0]} + {idx[1]} + C', 'A', [], nondet_init=False),
 'init-non-constant-3-u.c': standard(nnn, lambda idx: f'{el("A", idx)} == {idx[0]} + {idx[1]} + {idx[2]} + C', 'A', [], nondet_init=False),
 'max-2-u.c': {'loops': phase(mn, None, [arr_assigns('A', nn)]) + phase(nn, lambda idx: f'{el("A", idx)} <= max', ['max']) + check(nn, lambda idx: f'{el("A", idx)} <= max')},
 'max-3-n-u.c': {'loops': phase(mnp, None, [arr_assigns('A', mnp)]) + phase(mnp, lambda idx: f'{el("A", idx)} <= max', ['max']) + check(mnp, lambda idx: f'{el("A", idx)} <= max')},
 'min-2-u.c': {'loops': phase(mn, None, [arr_assigns('A', nn)]) + phase(nn, lambda idx: f'{el("A", idx)} >= min', ['min']) + check(nn, lambda idx: f'{el("A", idx)} >= min')},
 'min-3-n-u.c': {'loops': phase(mnp, None, [arr_assigns('A', mnp)]) + phase(mnp, lambda idx: f'{el("A", idx)} >= min', ['min']) + check(mnp, lambda idx: f'{el("A", idx)} >= min')},
 'rev-2-n-u.c': standard(mn, lambda idx: f'{el("A", idx)} == B[m-{idx[0]}-1][n-{idx[1]}-1]', 'A', ['B']),
 'rev-3-u.c': standard(nnn, lambda idx: f'{el("A", idx)} == B[n-{idx[0]}-1][n-{idx[1]}-1][n-{idx[2]}-1]', 'A', ['B']),
 'transpose-u.c': standard(nn, lambda idx: f'C[{idx[1]}][{idx[0]}] == A[{idx[0]}][{idx[1]}]', 'C', ['A']),
}
# the max and min phases keep the elements seen so far below max resp. above min; the check phases need all of them
ppp = ['p', 'p', 'p']
both = [done(ppp, copyP), done(nnn, copyP, lo=ppp)]
SPECS['copy-partial-3-u.c'] = {'loops': phase(nnn, None, [arr_assigns('B', nnn)]) + phase(ppp, copyP, [arr_assigns('A', nnn)])
   + phase(nnn, copyP, [arr_assigns('A', nnn)], lo=ppp, carry=[done(ppp, copyP)]) + phase(nnn, None, [], carry=both),
   'note': 'the two copies cover the cells below p and the cells at or above p in all coordinates; the assertion on the other cells is not implied by these invariants'}
# unsigned elements: the sums and differences wrap around, stated modulo 2^32
M32 = 4294967296
addU = lambda idx: f'({el("C", idx)} - ({el("A", idx)} + {el("B", idx)})) % {M32} == 0'
diffU = lambda idx: f'({el("C", idx)} - ({el("A", idx)} - {el("B", idx)})) % {M32} == 0'
SPECS['add-2-n-u.c'] = dict(standard(mn, addU, 'C', ['A', 'B']), note='the elements are unsigned, the sum is stated modulo 2^32')
SPECS['add-3-n-u.c'] = dict(standard(mnp, addU, 'C', ['A', 'B']), note='the elements are unsigned, the sum is stated modulo 2^32')
SPECS['diff-3-n-u.c'] = dict(standard(mnp, addU, 'C', ['A', 'B']), note='the elements are unsigned, the sum is stated modulo 2^32')
SPECS['diff-2-n-u.c'] = {'loops': phase(mn, None, [arr_assigns('A', mn)]) + phase(mn, None, [arr_assigns('B', mn)]) + phase(mn, diffU, [arr_assigns('C', mn)]) + check(mn, diffU),
   'note': 'the elements are unsigned, the difference is stated modulo 2^32'}
SPECS['init-non-constant-2-n-u.c'] = dict(standard(['q', 's'], lambda idx: f'({el("A", idx)} - ({idx[0]} + {idx[1]} + C)) % {M32} == 0', 'A', [], nondet_init=False), note='the elements are unsigned, stated modulo 2^32')
SPECS['init-non-constant-3-u.c'] = dict(standard(nnn, lambda idx: f'({el("A", idx)} - ({idx[0]} + {idx[1]} + {idx[2]} + C)) % {M32} == 0', 'A', [], nondet_init=False), note='the elements are unsigned, stated modulo 2^32')
