import os
ACSL = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
# the scaling variants of nla-digbench: the same programs with bounds on the inputs (valuebound) or on the number of
# iterations (unwindbound, a global counter), so the loop invariants of the base tasks apply unchanged
import importlib.util, os, re
p = os.path.join(os.path.dirname(__file__), 'nla_digbench.py')
s = importlib.util.spec_from_file_location('nla', p); nla = importlib.util.module_from_spec(s); s.loader.exec_module(nla)
BASE = {os.path.splitext(k)[0]: v for k, v in nla.SPECS.items()}
pow2 = lambda v, base='1': f'\\exists integer k; 0 <= k <= 64 && {v} == {base} * (1 << k)'
BASE.update({
 'freire1': {'loops': [['r*r - a - r + 2*x == 0', 'r >= 0', 'assigns x, r']], 'note': 'floating point, the invariant is exact in the reals'},
 'freire2': {'loops': [['4*s - 12*r*r == 1', '4*r*r*r - 6*r*r + 3*r + 4*x - 4*a == 1', '8*r*s - 24*a + 16*r - 12*s + 24*x - 3 == 0', 'r >= 1', 'assigns x, s, r']],
   'note': 'expected verdict false (rounding of the doubles), the invariants are exact in the reals'},
 'geo1-ll2': {'loops': [['x*z - x - y + 1 == 0', 'c >= 1', 'assigns x, y, c']]},
 'geo2-ll2': {'loops': [['1 + x*z - x - z*y == 0', 'c >= 1', 'assigns x, y, c']]},
 'hard2': {'loops': [['q == 0 && r == A', 'd == B*p', 'p >= 1', pow2('p'), 'assigns d, p'], ['A == q*B + r', 'd == B*p', 'r < d', 'r >= 0', 'p >= 1', pow2('p'), 'assigns r, d, p, q']],
   'note': 'p is a power of 2, written with a shift'},
})
SPECS = {}
d = os.path.join(ACSL, 'nla-digbench-scaling')
for f in sorted(os.listdir(d)):
    if not f.endswith(('.c', '.i')): continue
    base = re.sub(r'_(value|unwind)bound\d+', '', os.path.splitext(f)[0])
    spec = dict(BASE[base])
    kind = 'valuebound' if 'valuebound' in f else 'unwindbound'
    note = spec.get('note')
    spec['note'] = (f'the invariants of nla-digbench/{base}' + (f'; {note}' if note else ''))
    if kind == 'unwindbound':
        # the loops run at most N times: the counter is bounded
        n = re.search(r'unwindbound(\d+)', f).group(1)
        spec['loops'] = [cl + [f'0 <= counter <= {n} + 1'] for cl in spec['loops']]
        # the loop test counter++ < N assigns the counter, so it belongs to the assigns clause of the loop
        spec['loops'] = [[c + ', counter' if c.startswith('assigns ') and 'counter' not in c else c for c in cl]
                         for cl in spec['loops']]
    SPECS[f] = spec
