# shared templates: the reducer programs (a function folds an array, main checks that swapping and rotating the
# array does not change the result) and sums over arrays
import re

A = lambda lo, hi, body: f'\\forall integer t; {lo} <= t < {hi} ==> {body}'

def sum_axiomatic(name, typ):
    """a recursive logic function name(a, n) = a[0] + ... + a[n-1] over arrays of typ"""
    return f"""/*@ axiomatic {name.capitalize()} {{
  logic integer {name}({typ} *a, integer n) reads a[0..n-1];
  axiom {name}_zero: \\forall {typ} *a; {name}(a, 0) == 0;
  axiom {name}_step: \\forall {typ} *a, integer n; n >= 0 ==> {name}(a, n+1) == {name}(a, n) + a[n];
}} */
"""

# the step of the fold of each reducer, as a term in fold(x, n) and x[n]
STEPS = {
 'bAnd': ('fold(x, n) & x[n]', 1), 'bor': ('fold(x, n) | x[n]', 1), 'xor': ('fold(x, n) ^ x[n]', 1),
 'mapsum': ('fold(x, n) + n + x[n]', 0), 'mapavg': ('fold(x, n) + n + x[n]', 0),
 'sum': ('fold(x, n) + x[n]', 0), 'avg': ('fold(x, n) + x[n]', 0),
 'max': ('(fold(x, n) < x[n] ? x[n] : fold(x, n))', 0), 'sep': ('fold(x, n) + (x[n] % 2 == 0 ? 1 : -1)', 0),
}

def reducer(text, false=False):
    """the spec of a reducer program from its text: the function name and the size"""
    m = re.search(r'int\s+(\w+)\s*\(int x\[(\w+)\]\)', text)
    F, S = m.group(1), m.group(2)
    if F == 'rangesum':
        step, start = f'fold(x, n) + (n > {S}/2 ? x[n] : 0)', 0
    else:
        step, start = STEPS[F]
    base = f'fold(x, 1) == x[0]' if start == 1 else 'fold(x, 0) == 0'
    lemmas = '' if false else f"""  lemma fold_swap{{L1, L2}}: \\forall int *x, integer n; n >= 2 && \\at(x[0], L2) == \\at(x[1], L1) && \\at(x[1], L2) == \\at(x[0], L1)
    && (\\forall integer k; 2 <= k < n ==> \\at(x[k], L2) == \\at(x[k], L1)) ==> \\at(fold(x, n), L2) == \\at(fold(x, n), L1);
  lemma fold_rotate{{L1, L2}}: \\forall int *x, integer n; n >= 1 && (\\forall integer k; 0 <= k < n-1 ==> \\at(x[k], L2) == \\at(x[k+1], L1))
    && \\at(x[n-1], L2) == \\at(x[0], L1) ==> \\at(fold(x, n), L2) == \\at(fold(x, n), L1);
"""
    ax = f"""/*@ axiomatic Fold {{
  logic integer fold(int *x, integer n) reads x[0..n-1];
  axiom fold_base: \\forall int *x; {base};
  axiom fold_step: \\forall int *x, integer n; n >= {start} ==> fold(x, n+1) == {step};
{lemmas}}} */
"""
    if F in ('avg', 'mapavg'): result = f'\\result == (int) (fold(x, {S}) / {S})'
    elif F == 'rangesum': result = f'\\result == (int) ({S} - {S}/2 - 1 > 0 ? fold(x, {S}) / ({S} - {S}/2 - 1) : 0)'
    else: result = f'\\result == (int) fold(x, {S})'
    funcs = {F: [f'requires {S} >= 1', f'requires \\valid_read(x + (0..{S}-1))', 'assigns \\nothing', f'ensures {result}']}
    acc = 'res' if F in ('bAnd', 'bor', 'xor') else 'ret'
    inner = [f'{start} <= i <= {S}', f'{acc} == fold(x, i)', f'assigns i, {acc}']
    if F == 'rangesum': inner.insert(2, f'cnt == (i > {S}/2 + 1 ? i - {S}/2 - 1 : 0)')
    init = [f'0 <= i <= {S}', f'assigns i, x[0..{S}-1]']
    rot = [f'0 <= i <= {S}-1', f'\\forall integer k; 0 <= k < i ==> x[k] == \\at(x[k+1], L2)', f'\\forall integer k; i <= k < {S} ==> x[k] == \\at(x[k], L2)',
           f'temp == \\at(x[0], L2)', f'assigns i, x[0..{S}-2]']
    loops = [init, inner, rot] if 'init_nondet' in text else ([inner, init, rot] if re.search(r'x\[i\]\s*=\s*__VERIFIER_nondet', text) else [inner, rot])
    # the init loop is in init_nondet (first in the file) for rangesum, after the function otherwise; the order in
    # the file is the order of the functions
    if 'init_nondet' in text:
        funcs['init_nondet'] = [f'requires {S} >= 1', f'requires \\valid(x + (0..{S}-1))', f'assigns x[0..{S}-1]']
    ghost = {m.group(0): ax, f'ret = {F}(x);': 'L1: ;\n'}
    if not false:
        ghost[f'ret2 = {F}(x);'] = f'//@ assert fold(x, {S}) == \\at(fold(x, {S}), L1);\nL2: ;\n'
        ghost[f'ret5 = {F}(x);'] = f'//@ assert fold(x, {S}) == \\at(fold(x, {S}), L2);\n'
    else:
        ghost[f'ret2 = {F}(x);'] = 'L2: ;\n'
    note = f'the result of {F} is the logic function fold of the axiomatic Fold' + ('' if false else ', invariant under the swap and the rotation by the lemmas fold_swap and fold_rotate (labels L1, L2)')
    if false: note = 'expected verdict false (the sum of a range is not invariant under rotation); ' + note
    return {'loops': loops, 'funcs': funcs, 'ghost': ghost, 'note': note}

def zero_sum(text, const):
    """zero_sum*: a sum of the elements added and subtracted in loops"""
    S = 'SIZE'
    signs = re.findall(r'sum = sum ([+-]) a\[i\]', text)
    if const:
        loops = [[f'0 <= i <= {S}', A('0', 'i', 'a[t] == 1'), f'assigns i, a[0..{S}-1]']]
        total = lambda c: f'{c}*{S}'; part = 'i'
    else:
        loops = [[f'0 <= i <= {S}', f'assigns i, a[0..{S}-1]']]
        total = lambda c: f'{c}*sum(a, {S})'; part = 'sum(a, i)'
    c = 0
    for s in signs:
        inv = [f'0 <= i <= {S}', f'sum == {total(c)} {s} {part}', 'assigns i, sum']
        if const: inv.insert(1, A('0', S, 'a[t] == 1'))
        loops.append(inv)
        c += 1 if s == '+' else -1
    spec = {'loops': loops}
    if not const:
        spec['ghost'] = {'int main()': sum_axiomatic('sum', 'short')}
        spec['note'] = 'the partial sums are the logic function sum of the axiomatic Sum'
    return spec
