import os, re
ACSL = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))  # benchmarks/acsl
D = os.path.join(ACSL, 'array-patterns')
N = 'ARR_SIZE'
ASUM = """/*@ axiomatic Asum {
  logic integer asum(int *a, integer n) reads a[0..n-1];
  axiom asum_zero: \\forall int *a; asum(a, 0) == 0;
  axiom asum_step: \\forall int *a, integer n; n >= 0 ==> asum(a, n+1) == asum(a, n) + a[n];
  logic integer sqsum(int *a, integer n) reads a[0..n-1];
  axiom sqsum_zero: \\forall int *a; sqsum(a, 0) == 0;
  axiom sqsum_step: \\forall int *a, integer n; n >= 0 ==> sqsum(a, n+1) == sqsum(a, n) + a[n]*a[n];
%s} */
"""
MSUM = """/*@ axiomatic Msum {
  logic integer rsum(int *r, integer n) reads r[0..n-1];
  axiom rsum_zero: \\forall int *r; rsum(r, 0) == 0;
  axiom rsum_step: \\forall int *r, integer n; n >= 0 ==> rsum(r, n+1) == rsum(r, n) + r[n];
  // the sum of the first rows of a matrix with n columns, flattened
  logic integer msum(int *a, integer n, integer rows) reads a[0..n*rows-1];
  axiom msum_zero: \\forall int *a, integer n; msum(a, n, 0) == 0;
  axiom msum_step: \\forall int *a, integer n, integer rows; rows >= 0 ==> msum(a, n, rows+1) == msum(a, n, rows) + rsum(a + rows*n, n);
%s} */
"""
def lemma1(E, bound):
    # E(a1, a2, n, t): the element-wise property, bound(s): the bound of the total sum s
    return f"  lemma total: \\forall int *a1, int *a2, integer n; n >= 1 && (\\forall integer t; 0 <= t < n ==> {E('a1', 'a2', 'n', 't')}) ==> {bound('asum(a1, n) + asum(a2, n)')};\n"
def lemma2(E2, bound):
    # E2(cell, n, r, c) with cell(r, c) the element
    cell = lambda r, c: f'a[({r})*n + ({c})]'
    return f"  lemma total: \\forall int *a, integer n; n >= 1 && (\\forall integer r, c; 0 <= r < n && 0 <= c < n ==> {E2(cell, 'n', 'r', 'c')}) ==> {bound('msum(a, n, n)')};\n"

def one_d(E, bound, init=('0', '0'), count_cycle=False, extra_assigns='', squares=False, false=None):
    """init loop (array1, array2 := init), the while loop with the element-wise property E, the sum loop"""
    e_inv = f'\\forall integer t; 0 <= t < {N} ==> {E("array1", "array2", N, "t")}'
    init_inv = [f'0 <= count <= {N}', f'\\forall integer t; 0 <= t < count ==> array1[t] == {init[0]} && array2[t] == {init[1]}', f'assigns count, array1[0..{N}-1], array2[0..{N}-1]']
    while_inv = [e_inv] + (['1 <= count <= 200'] if count_cycle else []) + [f'assigns index, temp, array1[0..{N}-1], array2[0..{N}-1]' + extra_assigns]
    if squares:
        sum_inv = [f'0 <= count <= {N}', e_inv, 'sum1 == sqsum(array1, count)', 'sum2 == sqsum(array2, count)', 'assigns count, sum1, sum2']
    else:
        sum_inv = [f'0 <= count <= {N}', e_inv, 'sum == asum(array1, count) + asum(array2, count)', 'assigns count, sum']
    spec = {'loops': [init_inv, while_inv, sum_inv], 'ghost': {'int main()': ASUM % ('' if false or bound is None else lemma1(E, bound))},
            'note': 'the sums are the logic functions of the axiomatic Asum, the final bound follows from the element-wise property by the lemma total'}
    if false: spec['note'] = f'expected verdict false ({false}); the element-wise property that still holds and the sums as logic functions'
    return spec

def two_d(E2, bound, nloops=5, funcs=None, false=None, extra=''):
    cell = lambda r, c: f'array[{r}][{c}]'
    e_inv = f'\\forall integer r, c; 0 <= r < {N} && 0 <= c < {N} ==> {E2(cell, N, "r", "c")}'
    init_o = [f'0 <= row <= {N}', f'\\forall integer r, c; 0 <= r < row && 0 <= c < {N} ==> array[r][c] == 0', f'assigns row, column, array[0..{N}-1][0..{N}-1]']
    init_i = [f'0 <= column <= {N}', f'0 <= row < {N}', f'\\forall integer r, c; 0 <= r < row && 0 <= c < {N} ==> array[r][c] == 0', f'\\forall integer c; 0 <= c < column ==> array[row][c] == 0', f'assigns column, array[row][0..{N}-1]']
    while_inv = [e_inv, f'assigns index1, index2, temp, array[0..{N}-1][0..{N}-1]' + extra]
    sum_o = [f'0 <= row <= {N}', e_inv, f'sum == msum((int *) array, {N}, row)', 'assigns row, column, sum']
    sum_i = [f'0 <= column <= {N}', f'0 <= row < {N}', e_inv, f'sum == msum((int *) array, {N}, row) + rsum(array[row], column)', 'assigns column, sum']
    spec = {'loops': [init_o, init_i, while_inv, sum_o, sum_i], 'ghost': {'int main()': MSUM % ('' if false else lemma2(E2, bound))},
            'note': 'the sums are the logic functions of the axiomatic Msum over the flattened matrix, the final bound follows from the element-wise property by the lemma total'}
    if funcs: spec['funcs'] = funcs
    if false: spec['note'] = f'expected verdict false ({false})'
    return spec

def det_2d(content, sum_outer, sum_inner, funcs=None, value=None):
    """array25-30: deterministic contents and closed forms of the row-major partial sums"""
    c = lambda hi_r, part: [f'\\forall integer r, c; 0 <= r < {hi_r} && 0 <= c < {N} ==> array[r][c] == {content("r", "c")}'] + ([part] if part else [])
    init_o = [f'0 <= row <= {N}'] + c('row', None) + ([value('row', '0')] if value else []) + [f'assigns row, column, array[0..{N}-1][0..{N}-1]' + (', value' if value else '')]
    init_i = [f'0 <= column <= {N}', f'0 <= row < {N}'] + c('row', f'\\forall integer c; 0 <= c < column ==> array[row][c] == {content("row", "c")}') + ([value('row', 'column')] if value else []) + [f'assigns column, array[row][0..{N}-1]' + (', value' if value else '')]
    sum_o = [f'0 <= row <= {N}'] + c(N, None) + [sum_outer, 'assigns row, column, sum']
    sum_i = [f'0 <= column <= {N}', f'0 <= row < {N}'] + c(N, None) + [sum_inner, 'assigns column, sum']
    spec = {'loops': [init_o, init_i, sum_o, sum_i], 'note': 'the partial sums in row-major order in closed form'}
    if funcs: spec['funcs'] = funcs
    return spec

boundary = {'outerBoundaryPatternCheck': ['assigns \\nothing', f'ensures \\result == ((index == 0 || index == {N}-1) ? 1 : 0)']}
pair_rev = lambda a1, a2, n, t: f'{a1}[{t}] + {a2}[{n}-1-{t}] == 0'
pair = lambda a1, a2, n, t: f'{a1}[{t}] + {a2}[{t}] == 0'
Sp = lambda r, c: f'(((({r})+1)/2)*(({N}+1)/2) + (({r})/2)*({N}/2) + (({r}) % 2 == 0 ? (({c})+1)/2 : ({c})/2))'
SPECS = {
 'array1_pattern.c': one_d(lambda a1, a2, n, t: f'({a1}[{t}] == 0 && {a2}[{n}-1-{t}] == 0) || ({a1}[{t}] == {t} && {a2}[{n}-1-{t}] == -({t}))', lambda s: f'{s} == 0'),
 'array1_pattern_buggy.c': one_d(lambda a1, a2, n, t: f'({a1}[{t}] == 0 || {a1}[{t}] == {t}) && ({a2}[{t}] == 0 || {a2}[{t}] == -({n}-1-{t}))', None, false='array1[42] stays 0'),
 'array2_pattern.c': one_d(pair_rev, lambda s: f'{s} == 0'),
 'array2_pattern_buggy.c': one_d(lambda a1, a2, n, t: f'{a1}[{t}] >= 0 && {a2}[{t}] <= 0', None, false='array1[42] stays 0'),
 'array3_pattern.c': dict(one_d(pair_rev, None, squares=True), funcs={'square': ['assigns \\nothing', 'ensures \\result == x*x']}),
 'array3_pattern_buggy.c': dict(one_d(lambda a1, a2, n, t: f'{a1}[{t}] >= 0 && {a2}[{t}] <= 0', None, squares=True, false='array1[42] stays 0'), funcs={'square': ['assigns \\nothing', 'ensures \\result == x*x']}),
 'array5_pattern.c': one_d(pair, lambda s: f'{s} == 0', count_cycle=True, extra_assigns=', count'),
 'array5_pattern_buggy.c': one_d(lambda a1, a2, n, t: f'{t} % 2 == 1 ==> {a1}[{t}] + {a2}[{t}] == 0', None, count_cycle=True, extra_assigns=', count', false='array1[42] stays 0'),
 'array6_pattern.c': one_d(pair, lambda s: f'{s} == 0', init=('count', '-count')),
 'array6_pattern_buggy.c': one_d(lambda a1, a2, n, t: f'\\true', None, init=('count', '-count'), false='array1[42] is reset to 0'),
 'array7_pattern.c': one_d(pair, lambda s: f'{s} == 0', init=('count', '-count'), extra_assigns=', pivot'),
 'array7_pattern_buggy.c': one_d(lambda a1, a2, n, t: f'\\true', None, init=('count', '-count'), extra_assigns=', pivot', false='array1[42] is reset to 0'),
 'array8_pattern.c': one_d(lambda a1, a2, n, t: f'({t} % 2 == 1 ==> {a1}[{t}] + {a2}[{t}] == 0) && ({t} % 2 == 0 ==> ({a1}[{t}] == 0 || {a1}[{t}] == 1) && {a2}[{t}] == 0)', lambda s: f'2*({s}) <= n + 1'),
 'array9_pattern.c': one_d(lambda a1, a2, n, t: f'({t} % 3 != 0 ==> {a1}[{t}] + {a2}[{t}] == 0) && ({t} % 3 == 0 ==> ({a1}[{t}] == 0 || {a1}[{t}] == 1) && {a2}[{t}] == 0)', lambda s: f'3*({s}) <= n + 2'),
 'array10_pattern.c': one_d(lambda a1, a2, n, t: f'({t} % 2 == 1 ==> {a1}[{t}] + {a2}[{t}] == 0) && ({t} % 2 == 0 ==> ({a1}[{t}] == 0 || {a1}[{t}] == {t}) && {a2}[{t}] == 0)', lambda s: f'4*({s}) <= (n-1)*(n+1)'),
 'array11_pattern.c': one_d(lambda a1, a2, n, t: f'({t} != {n}-1 ==> {a1}[{t}] + {a2}[{t}] == 0) && ({t} == {n}-1 ==> {a1}[{t}] == {a2}[{t}] && ({a1}[{t}] == 0 || {a1}[{t}] == {t}))', lambda s: f'{s} == 0 || {s} + 2 == 2*n'),
 'array12_pattern.c': two_d(lambda a, n, r, c: f'({r} != {c} ==> {a(r, c)} + {a(c, r)} == 0 && -1 <= {a(r, c)} <= 1) && ({r} == {c} ==> ({a(r, c)} == 0 || {a(r, c)} == 1))', lambda s: f'0 <= {s} <= n'),
 'array13_pattern.c': two_d(lambda a, n, r, c: f'({r} > {c} ==> 0 <= {a(r, c)} <= 1) && ({r} <= {c} ==> {a(r, c)} == 0)', lambda s: f'2*({s}) <= n*(n-1)'),
 'array14_pattern.c': two_d(lambda a, n, r, c: f'({r} + {c} == {n}-1 ==> 0 <= {a(r, c)} <= 1) && ({r} + {c} != {n}-1 ==> {a(r, c)} == 0)', lambda s: f'0 <= {s} <= n'),
 'array15_pattern.c': two_d(lambda a, n, r, c: f'(({r} + {c} == {n}-2 || {r} + {c} == {n}) ==> 0 <= {a(r, c)} <= 1) && (({r} + {c} != {n}-2 && {r} + {c} != {n}) ==> {a(r, c)} == 0)', lambda s: f'{s} <= 2*(n-1)'),
 'array16_pattern.c': two_d(lambda a, n, r, c: f'(({r} == {c} || {r} + {c} == {n}-1) ==> 0 <= {a(r, c)} <= 1) && (({r} != {c} && {r} + {c} != {n}-1) ==> {a(r, c)} == 0)', lambda s: f'{s} <= 2*n'),
 'array17_pattern.c': two_d(lambda a, n, r, c: f'({r} != {c} && {r} + {c} != {n}-1 ==> {a(r, c)} == 0) && ({r} == {c} && {r} + {c} != {n}-1 ==> ({a(r, c)} == 0 || {a(r, c)} == -1) && {a(r, c)} + {a(r, f"{n}-1-{c}")} == 0) && ({r} == {c} && {r} + {c} == {n}-1 ==> ({a(r, c)} == 0 || {a(r, c)} == 1))', lambda s: f'{s} == 0 || {s} == 1'),
 'array18_pattern.c': two_d(lambda a, n, r, c: f'({r} != {c} && {r} + {c} != {n}-1 ==> {a(r, c)} == 0) && ({r} == {c} && {r} + {c} != {n}-1 ==> ({a(r, c)} == 0 || {a(r, c)} == -1) && {a(r, c)} + {a(f"{n}-1-{r}", c)} == 0) && ({r} == {c} && {r} + {c} == {n}-1 ==> ({a(r, c)} == 0 || {a(r, c)} == 1))', lambda s: f'{s} == 0 || {s} == 1'),
 'array19_pattern.c': two_d(lambda a, n, r, c: f'({r} != {c} && {r} + {c} != {n}-1 ==> {a(r, c)} == 0) && ({r} + {c} == {n}-1 && {r} != {c} ==> ({a(r, c)} == 0 || {a(r, c)} == -1) && {a(r, c)} + {a(r, r)} == 0) && ({r} == {c} && {r} + {c} == {n}-1 ==> ({a(r, c)} == 0 || {a(r, c)} == 1))', lambda s: f'{s} == 0 || {s} == 1'),
 'array20_pattern.c': two_d(lambda a, n, r, c: f'({r} != {c} && {r} + {c} != {n}-1 ==> {a(r, c)} == 0) && ({r} + {c} == {n}-1 && {r} != {c} ==> ({a(r, c)} == 0 || {a(r, c)} == -1) && {a(r, c)} + {a(c, c)} == 0) && ({r} == {c} && {r} + {c} == {n}-1 ==> ({a(r, c)} == 0 || {a(r, c)} == 1))', lambda s: f'{s} == 0 || {s} == 1'),
 'array21_pattern.c': two_d(lambda a, n, r, c: f'(({r} == 0 || {r} == {n}-1 || {c} == 0 || {c} == {n}-1) ==> 0 <= {a(r, c)} <= 1) && (({r} != 0 && {r} != {n}-1 && {c} != 0 && {c} != {n}-1) ==> {a(r, c)} == 0)', lambda s: f'{s} <= 4*(n-1)', funcs=boundary),
 'array22_pattern.c': two_d(lambda a, n, r, c: f'((0 < {c} && {c} < {n}-1) ==> {a(r, c)} == 0) && ({c} == 0 ==> {a(r, c)} + {a(r, f"{n}-1")} == 0 && -1 <= {a(r, c)} <= 1)', lambda s: f'{s} == 0', funcs=boundary),
 'array23_pattern.c': two_d(lambda a, n, r, c: f'((0 < {r} && {r} < {n}-1) ==> {a(r, c)} == 0) && ({r} == 0 ==> {a(r, c)} + {a(f"{n}-1", c)} == 0 && -1 <= {a(r, c)} <= 1)', lambda s: f'{s} == 0', funcs=boundary),
 'array24_pattern.c': two_d(lambda a, n, r, c: f'((0 < {r} && {r} < {n}-1 && 0 < {c} && {c} < {n}-1) ==> 0 <= {a(r, c)} <= 1) && (({r} == 0 || {r} == {n}-1 || {c} == 0 || {c} == {n}-1) ==> {a(r, c)} == 0)', lambda s: f'0 <= {s} <= (n-2)*(n-2)', funcs=boundary),
 'array25_pattern.c': det_2d(lambda r, c: f'(({r}) % 2 == 0 && ({c}) % 2 == 0 ? 1 : (({r}) % 2 == 1 && ({c}) % 2 == 1 ? -1 : 0))',
   f'sum == ((row+1)/2)*(({N}+1)/2) - (row/2)*({N}/2)', f'sum == ((row+1)/2)*(({N}+1)/2) - (row/2)*({N}/2) + (row % 2 == 0 ? (column+1)/2 : -(column/2))'),
 'array26_pattern.c': det_2d(lambda r, c: f'(({r}) % 2 == ({c}) % 2 ? ({Sp(r, c)} % 2 == 0 ? 1 : -1) : 0)', f'sum == {Sp("row", "0")} % 2', f'sum == {Sp("row", "column")} % 2',
   value=lambda r, c: f'value == ({Sp(r, c)} % 2 == 0 ? 1 : -1)'),
 'array27_pattern.c': det_2d(lambda r, c: f'(({r}) == ({c}) ? 0 : ({r}))', f'2*sum == ({N}-1)*row*(row-1)', f'2*sum == ({N}-1)*row*(row-1) + 2*row*(column - (column > row ? 1 : 0))'),
 'array28_pattern.c': two_d(lambda a, n, r, c: f'{a(r, c)} == ({r} > {c} ? {r} + {c} : ({r} < {c} ? -({r} + {c}) : 0))', lambda s: f'{s} == 0'),
 'array29_pattern.c': det_2d(lambda r, c: f'(({r}) == ({c}) ? 0 : ({c}))', f'2*sum == row*{N}*({N}-1) - row*(row-1)', f'2*sum == row*{N}*({N}-1) - row*(row-1) + column*(column-1) - 2*(column > row ? row : 0)'),
 'array30_pattern.c': det_2d(lambda r, c: f'(({r}) > ({c}) ? ({r}) - ({c}) : ({c}) - ({r}))',
   f'6*sum == (row-1)*row*(row+1) + ({N}-1)*{N}*({N}+1) - ({N}-row-1)*({N}-row)*({N}-row+1)',
   f'6*sum == (row-1)*row*(row+1) + ({N}-1)*{N}*({N}+1) - ({N}-row-1)*({N}-row)*({N}-row+1) + (column <= row ? 6*row*column - 3*column*(column-1) : 3*row*(row+1) + 3*(column-1-row)*(column-row))',
   funcs={'diff': ['assigns \\nothing', 'ensures \\result == (idx1 > idx2 ? idx1 - idx2 : idx2 - idx1)']}),
}
# array28 is deterministic but antisymmetric: the zero total follows from the element-wise property with Msum; its
# init loops write the pattern, not zeros
SPECS['array28_pattern.c']['loops'][0] = [f'0 <= row <= {N}', f'\\forall integer r, c; 0 <= r < row && 0 <= c < {N} ==> array[r][c] == (r > c ? r + c : (r < c ? -(r + c) : 0))', f'assigns row, column, array[0..{N}-1][0..{N}-1]']
SPECS['array28_pattern.c']['loops'][1] = [f'0 <= column <= {N}', f'0 <= row < {N}', f'\\forall integer r, c; 0 <= r < row && 0 <= c < {N} ==> array[r][c] == (r > c ? r + c : (r < c ? -(r + c) : 0))', f'\\forall integer c; 0 <= c < column ==> array[row][c] == (row > c ? row + c : (row < c ? -(row + c) : 0))', f'assigns column, array[row][0..{N}-1]']
del SPECS['array28_pattern.c']['loops'][2]
# array4: both arrays are updated at zero positions with count and -count, so the total of the sums is invariant
E4 = lambda a1, a2, n, t: '\\true'
for f, false in (('array4_pattern.c', None), ('array4_pattern_buggy.c', 'array1[42] stays 0')):
    spec = one_d(E4, None, count_cycle=True, extra_assigns=', count, index1, index2', false=false)
    spec['loops'][1] = ([f'asum(array1, {N}) + asum(array2, {N}) == 0'] if not false else []) + ['1 <= count <= 200', f'assigns index1, index2, temp, count, array1[0..{N}-1], array2[0..{N}-1]']
    spec['loops'][2] = [f'0 <= count <= {N}'] + ([f'asum(array1, {N}) + asum(array2, {N}) == 0'] if not false else []) + ['sum == asum(array1, count) + asum(array2, count)', 'assigns count, sum']
    update = "  lemma asum_update{L1, L2}: \\forall int *a, integer n, k; 0 <= k < n && (\\forall integer t; 0 <= t < n && t != k ==> \\at(a[t], L2) == \\at(a[t], L1)) ==> \\at(asum(a, n), L2) == \\at(asum(a, n), L1) + \\at(a[k], L2) - \\at(a[k], L1);\n"
    spec['ghost'] = {'int main()': ASUM % update}
    if not false: spec['note'] = 'the total of the two sums is a loop invariant (each iteration adds count and -count at zero positions, lemma asum_update)'
    SPECS[f] = spec
