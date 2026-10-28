import os, re
ACSL = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))  # benchmarks/acsl
D = os.path.join(ACSL, 'array-examples')
N = 100000
A = lambda lo, hi, body: f'\\forall integer t; {lo} <= t < {hi} ==> {body}'
ALL = lambda body: A('0', N, body)
init = lambda v, *arrs: [f'0 <= {v} <= {N}', 'assigns ' + ', '.join([v] + [f'{a}[0..{N-1}]' for a in arrs])]
chk = lambda v, *facts: [f'0 <= {v} <= {N}'] + list(facts) + [f'assigns {v}']
F = lambda spec, why: dict(spec, note='expected verdict false (' + why + ')')
sorted_ = lambda hi: f'\\forall integer p, q; 0 <= p < q < {hi} ==> a[p] <= a[q]'
distinct = lambda hi: f'\\forall integer p, q; 0 <= p < q < {hi} ==> set[p] != set[q]'

def dsset(found_result, trivial):
    ex = ['requires 0 <= size <= 100000', 'requires \\valid_read(set + (0..size-1))', 'assigns \\nothing',
          f'ensures (\\result == {found_result}) <==> (\\exists integer t; 0 <= t < size && set[t] == value)',
          f'ensures \\result == {found_result} || \\result == {1 - found_result}']
    ins = ['requires 0 <= size < 100000', 'requires \\valid(set + size)', 'assigns set[size]', 'ensures \\result == size + 1', 'ensures set[size] == value']
    funcs = {'insert': ins, 'elem_exists': ex}
    exloop = ['0 <= i <= size', A('0', 'i', 'set[t] != value'), 'assigns i']
    outer = lambda: ['0 <= x <= n', distinct('n'), 'assigns x, y']
    inner = lambda: ['x < y <= n', distinct('n'), 'assigns y']
    main = [exloop, init('x', 'set'), outer(), inner(), init('v', 'values'),
            [f'0 <= v <= {N}', '0 <= n <= v', distinct('n'), 'assigns v, n, set[0..99999]']]
    if trivial: main.append(['0 <= x <= n', 'n == 0', 'assigns x, y']); main.append(['x < y <= n', 'assigns y'])
    main += [outer(), inner()]
    if trivial:
        main[5] = [f'0 <= v <= {N}', 'n == 0', 'assigns v, n, set[0..99999]']
    return {'loops': main, 'funcs': funcs}

def copies(text):
    """standard_copyK: a chain of copies a1 -> a2 -> ..., the known arrays equal a1"""
    pairs = re.findall(r'(a\d)\[i\] = (a\d)\[i\];', text)
    loops = [init('a', 'a1')]
    known = ['a1']
    for dst, src in pairs:
        facts = [ALL(f'{k}[t] == a1[t]') for k in known if k != 'a1']
        loops.append([f'0 <= i <= {N}'] + facts + [A('0', 'i', f'{dst}[t] == {src}[t]'), f'assigns i, {dst}[0..{N-1}]'])
        if src in known and dst not in known: known.append(dst)
        elif src not in known and dst in known: known.remove(dst)
    last = pairs[-1][0]
    facts = [ALL(f'{k}[t] == a1[t]') for k in known if k != 'a1']
    loops.append(chk('x', *facts))
    spec = {'loops': loops}
    return spec if last in known else F(spec, f'{last} is not a copy of a1')

def inits(text, expected):
    vals = [int(v) for v in re.findall(r'a\[i\] = (\d+);', text)]
    loops = []
    for k, v in enumerate(vals):
        inv = [f'0 <= i <= {N}', A('0', 'i', f'a[t] == {v}')]
        if k > 0: inv.append(A('i', N, f'a[t] == {vals[k-1]}'))
        loops.append(inv + [f'assigns i, a[0..{N-1}]'])
    loops.append(chk('x', ALL(f'a[t] == {vals[-1]}')))
    spec = {'loops': loops}
    return spec if expected == vals[-1] else F(spec, f'the elements are {vals[-1]}')

def two_index(s, size):
    if s == 1:
        rel = lambda hi: f'\\forall integer t; 0 <= t < {hi} ==> a[t] == b[t]'
        return {'loops': [[f'0 <= i <= {size}', f'assigns i, b[0..{size-1}]'],
          [f'0 <= i <= {size}', 'i == j', rel('j'), f'assigns i, j, a[0..{size-1}]'], [f'0 <= i <= {size}', 'i == j', rel(size), 'assigns i, j']]}
    rel = lambda hi: f'\\forall integer t; 0 <= t < {hi} ==> a[t] == b[{s}*t+1]'
    return {'loops': [[f'0 <= i <= {size}', f'assigns i, b[0..{size-1}]'],
      [f'i == {s}*j + 1', '0 <= j', rel('j'), f'assigns i, j, a[0..{size-1}]'],
      [f'i == {s}*j + 1', '0 <= j', f'\\forall integer t; 0 <= t && {s}*t+1 < {size} ==> a[t] == b[{s}*t+1]', 'assigns i, j']]}

bubble_bounds = [init('j', 'a'), ['swapped == 0 || swapped == 1', f'assigns swapped, i, a[0..{N-1}]'], [f'1 <= i <= {N}', f'assigns i, swapped, a[0..{N-1}]'],
                 [f'0 <= x <= {N}', 'assigns x, y'], [f'x < y <= {N}', 'assigns y']]
sel_bounds = [init('i', 'a'), [f'0 <= i <= {N}', f'assigns i, k, s, x, y, a[0..{N-1}]'], [f'i <= k <= {N}', f'i <= s < {N}', 'assigns k, s'],
              ['0 <= x <= i', 'assigns x, y'], ['x < y <= i', 'assigns y'], [f'i <= x <= {N}', 'assigns x'], [f'0 <= x <= {N}', 'assigns x, y'], [f'x < y <= {N}', 'assigns y']]
prefix_le = 'sorted: ' + sorted_('i')
sel_facts = [sorted_('i'), f'\\forall integer p, q; 0 <= p < i && i <= q < {N} ==> a[p] <= a[q]']
sel_facts2 = [f'\\forall integer p, q; 0 <= p < q <= i ==> a[p] <= a[q]', f'\\forall integer t; i <= t < {N} ==> a[i] <= a[t]']
selection = [init('i', 'a'),
  [f'0 <= i <= {N}'] + sel_facts + [f'assigns i, k, s, x, y, a[0..{N-1}]'],
  [f'i + 1 <= k <= {N}', f'i <= s < {N}', '\\forall integer t; i <= t < k ==> a[s] <= a[t]'] + sel_facts + ['assigns k, s'],
  ['0 <= x <= i'] + sel_facts2 + ['assigns x, y'], ['x < y <= i'] + sel_facts2 + ['assigns y'], [f'i <= x <= {N}'] + sel_facts2 + ['assigns x'],
  chk('x', sorted_(N)) + ['assigns x, y'], [f'x < y <= {N}', sorted_(N), 'assigns y']]
selection[6] = [f'0 <= x <= {N}', sorted_(N), 'assigns x, y']
partition1 = [[f'0 <= a <= {N}', '0 <= b <= a', A('0', 'b', 'bb[t] >= 0'), f'assigns a, b, bb[0..{N-1}]']]
SPECS = {
 'data_structures_set_multi_proc_ground-1.i': F(dsset(0, False), 'elem_exists returns 0 when the element exists'),
 'data_structures_set_multi_proc_ground-2.i': dsset(1, False),
 'data_structures_set_multi_proc_trivial_ground.i': dict(dsset(1, True), note='no element is ever inserted (n stays 0)'),
 'relax-2-2.i': {'loops': 'skip', 'note': 'relaxed prefix with pointers and unsigned long, only the harness is annotated'},
 'sanfoundry_02_ground.i': {'loops': [init('i', 'array'),
   [f'2 <= i <= {N}', 'largest2 <= largest1', A('0', 'i', 'array[t] <= largest1'), A('0', 'i', 'array[t] <= largest2 || array[t] == largest1'), 'assigns i, largest1, largest2'],
   chk('x', ALL('array[t] <= largest1')), chk('x', ALL('array[t] <= largest2 || array[t] == largest1'))]},
 'sanfoundry_10_ground.c': {'loops': [['0 <= i <= n', 'assigns i, vectorx[0..n-1]'],
   ['0 <= i <= n', 'found == 0 || found == 1', f'found == 0 ==> ({A("0", "i", "vectorx[t] != element")})',
    f'found == 1 ==> (0 <= pos < i && vectorx[pos] == element && ({A("0", "pos", "vectorx[t] != element")}))', 'assigns i, found, pos'],
   ['pos <= i <= n - 1', '0 <= pos', A('0', 'pos', 'vectorx[t] != element'), 'assigns i, vectorx[pos..n-1]'],
   ['0 <= x <= pos', A('0', 'pos', 'vectorx[t] != element'), 'assigns x']]},
 'sanfoundry_24-1.i': {'loops': [['0 <= i', 'i <= num || i == 0', 'assigns i, array[0..99999]'], ['0 <= i', 'i <= num || i == 0', 'assigns i'], ['0 <= i', 'i <= num || i == 0', 'assigns i']],
   'funcs': {'printEven': ['requires i % 2 == 0', 'assigns \\nothing'], 'printOdd': ['requires i % 2 != 0', 'assigns \\nothing']}},
 'sanfoundry_27_ground.i': {'loops': [init('i', 'array'), [f'1 <= i <= {N}', A('0', 'i', 'array[t] <= largest'), 'assigns i, largest'], chk('x', ALL('array[t] <= largest'))]},
 'sanfoundry_43_ground.i': {'loops': [[f'0 <= i <= {N}', A('0', 'i', 'dst[t] == src[t] + 1'), f'assigns i, dst[0..{N-1}]'], init('i', 'src'),
   chk('x', ALL('dst[t] == src[t] + 1')) + [f'assigns x, src[0..{N-1}]']],
   'funcs': {'incrementArray': [f'requires \\valid_read(src + (0..{N-1}))', f'requires \\valid(dst + (0..{N-1}))', f'requires \\separated(src + (0..{N-1}), dst + (0..{N-1}))',
     f'assigns dst[0..{N-1}]', f'ensures {ALL("dst[t] == src[t] + 1")}']}},
 'sorting_bubblesort_2_ground.i': F({'loops': bubble_bounds}, 'sorts in descending order'),
 'sorting_bubblesort_ground-1.i': {'loops': [init('j', 'a'), ['swapped == 0 || swapped == 1', f'swapped == 0 ==> ({sorted_(N)})', f'assigns swapped, i, a[0..{N-1}]'],
   [f'1 <= i <= {N}', 'swapped == 0 || swapped == 1', f'swapped == 0 ==> ({sorted_("i")})', f'assigns i, swapped, a[0..{N-1}]'],
   [f'0 <= x <= {N}', sorted_(N), 'assigns x, y'], [f'x < y <= {N}', sorted_(N), 'assigns y']]},
 'sorting_bubblesort_ground-2.i': F({'loops': bubble_bounds}, 'sorts in descending order'),
 'sorting_selectionsort_2_ground.i': F({'loops': sel_bounds}, 'the inner loop starts at k == i and compares with a[i+1]'),
 'sorting_selectionsort_ground-1.i': F({'loops': sel_bounds}, 'a[x] >= a[i] is asserted for x < i'),
 'sorting_selectionsort_ground-2.i': {'loops': selection},
 'standard_allDiff2_ground.i': F({'loops': [init('i', 'a'), [f'1 <= i <= {N}', 'r == 1', 'assigns i, j, r'], ['-1 <= j <= i - 1', 'r == 1', 'assigns j, r'],
   [f'0 <= x <= {N}', 'assigns x, y'], [f'x < y <= {N}', 'assigns y']]}, 'r stays 1 and the elements may coincide'),
 'standard_compare_ground.i': {'loops': [init('j', 'a', 'b'), [f'0 <= i <= {N}', 'rv == 0 || rv == 1', f'rv == 1 ==> ({A("0", "i", "a[t] == b[t]")})', 'assigns i, rv'],
   chk('x', ALL('a[t] == b[t]'))]},
 'standard_compareModified_ground.i': {'loops': [init('j', 'a', 'b'),
   [f'0 <= i <= {N}', 'rv == 0 || rv == 1', f'rv == 1 ==> ({A("0", "i", "a[t] == b[t]")})', A('0', 'i', 'c[t] == a[t]'), f'assigns i, rv, c[0..{N-1}]'],
   chk('x', ALL('a[t] == b[t]')), chk('x', ALL('c[t] == a[t]'))]},
 'standard_copyInit_ground.i': {'loops': [[f'0 <= i <= {N}', A('0', 'i', 'a[t] == 42'), f'assigns i, a[0..{N-1}]'],
   [f'0 <= i <= {N}', ALL('a[t] == 42'), A('0', 'i', 'b[t] == 42'), f'assigns i, b[0..{N-1}]'], chk('x', ALL('b[t] == 42'))]},
 'standard_copyInitSum2_ground-1.i': F({'loops': [[f'0 <= i <= {N}', A('0', 'i', 'a[t] == 42'), f'assigns i, a[0..{N-1}]'],
   [f'0 <= i <= {N}', ALL('a[t] == 42'), A('0', 'i', 'b[t] == 42'), f'assigns i, b[0..{N-1}]'],
   [f'0 <= i <= {N}', ALL('b[t] == 42'), A('0', 'i', 'a[t] == 42 + t'), f'assigns i, a[0..{N-1}]'], chk('x', ALL('b[t] == 42'))]}, 'b stays 42'),
 'standard_copyInitSum2_ground-2.i': {'loops': [[f'0 <= i <= {N}', A('0', 'i', 'a[t] == 42'), f'assigns i, a[0..{N-1}]'],
   [f'0 <= i <= {N}', ALL('a[t] == 42'), A('0', 'i', 'b[t] == 42'), f'assigns i, b[0..{N-1}]'],
   [f'0 <= i <= {N}', A('0', 'i', 'b[t] == 42 + t'), A('i', N, 'b[t] == 42'), f'assigns i, b[0..{N-1}]'], chk('x', ALL('b[t] == 42 + t'))]},
 'standard_copyInitSum3_ground.i': {'loops': [[f'0 <= i <= {N}', A('0', 'i', 'a[t] == 42'), f'assigns i, a[0..{N-1}]'],
   [f'0 <= i <= {N}', ALL('a[t] == 42'), A('0', 'i', 'b[t] == 42'), f'assigns i, b[0..{N-1}]'],
   [f'0 <= i <= {N}', ALL('a[t] == 42'), A('0', 'i', 'b[t] == 42 + t'), A('i', N, 'b[t] == 42'), f'assigns i, b[0..{N-1}]'],
   [f'0 <= i <= {N}', ALL('a[t] == 42'), A('0', 'i', 'b[t] == t'), A('i', N, 'b[t] == 42 + t'), f'assigns i, b[0..{N-1}]'], chk('x', ALL('b[t] == t'))]},
 'standard_copyInitSum_ground.i': {'loops': [[f'0 <= i <= {N}', A('0', 'i', 'a[t] == 42'), f'assigns i, a[0..{N-1}]'],
   [f'0 <= i <= {N}', ALL('a[t] == 42'), A('0', 'i', 'b[t] == 42'), f'assigns i, b[0..{N-1}]'],
   [f'0 <= i <= {N}', A('0', 'i', 'b[t] == 42 + incr'), A('i', N, 'b[t] == 42'), f'assigns i, b[0..{N-1}]'], chk('x', ALL('b[t] == 42 + incr'))]},
 'standard_find_ground-1.i': {'loops': [init('j', 'a'), [f'0 <= i <= {N}', A('0', 'i', 'a[t] != e'), 'assigns i'], ['0 <= x <= i', A('0', 'i', 'a[t] != e'), 'assigns x']]},
 'standard_maxInArray_ground.i': {'loops': [init('j', 'a'), [f'0 <= i <= {N}', A('0', 'i', 'a[t] <= max'), 'assigns i, max'], chk('x', ALL('a[t] <= max'))]},
 'standard_minInArray_ground-1.i': F({'loops': [init('j', 'a'), [f'0 <= i <= {N}', A('0', 'i', 'a[t] >= min'), 'assigns i, min'], chk('x', ALL('a[t] >= min'))]}, 'the minimum is not strictly above itself'),
 'standard_minInArray_ground-2.i': {'loops': [init('i', 'a'), [f'0 <= i <= {N}', A('0', 'i', 'a[t] >= min'), 'assigns i, min'], chk('x', ALL('a[t] >= min'))]},
 'standard_palindrome_ground.i': {'loops': [init('i', 'A'), [f'0 <= i <= {N//2}', A('0', 'i', f'A[t] == A[{N-1}-t]'), f'assigns i, A[0..{N//2-1}]'],
   [f'0 <= x <= {N//2}', A('0', N//2, f'A[t] == A[{N-1}-t]'), 'assigns x']]},
 'standard_partial_init_ground.i': {'loops': [init('i', 'A', 'B'), [f'0 <= i <= {N}', '0 <= j <= i', A('0', 'j', 't <= C[t] <= t + i - j'), f'assigns i, j, C[0..{N-1}]'],
   ['0 <= x <= j', '0 <= j <= i', A('0', 'j', 't <= C[t] <= t + i - j'), 'assigns x'], ['0 <= x <= j', A('0', 'j', 't <= C[t]'), 'assigns x']]},
 'standard_partition_ground-1.i': F({'loops': partition1 + [[f'0 <= a <= {N}', '0 <= c <= a', A('0', 'c', 'cc[t] >= 0'), A('0', 'b', 'bb[t] >= 0'), f'assigns a, c, cc[0..{N-1}]'],
   ['0 <= x <= b', A('0', 'b', 'bb[t] >= 0'), 'assigns x'], ['0 <= x <= c', A('0', 'c', 'cc[t] >= 0'), 'assigns x']]}, 'cc holds the nonnegative elements'),
 'standard_partition_ground-2.i': {'loops': [init('i', 'aa')] + partition1 + [[f'0 <= a <= {N}', '0 <= c <= a', A('0', 'c', 'cc[t] < 0'), A('0', 'b', 'bb[t] >= 0'), f'assigns a, c, cc[0..{N-1}]'],
   ['0 <= x <= b', A('0', 'b', 'bb[t] >= 0'), 'assigns x']]},
 'standard_partition_original_ground.i': {'loops': [init('i', 'aa'), [f'0 <= a <= {N}', '0 <= b', '0 <= c', 'b + c == a', A('0', 'b', 'bb[t] >= 0'), A('0', 'c', 'cc[t] < 0'), f'assigns a, b, c, bb[0..{N-1}], cc[0..{N-1}]'],
   ['0 <= x <= b', A('0', 'b', 'bb[t] >= 0'), 'assigns x'], ['0 <= x <= c', A('0', 'c', 'cc[t] < 0'), 'assigns x']]},
 'standard_password_ground.i': {'loops': [init('i', 'password', 'guess'), [f'0 <= i <= {N}', 'result == 0 || result == 1', f'result == 1 ==> ({A("0", "i", "password[t] == guess[t]")})', 'assigns i, result'],
   chk('x', ALL('password[t] == guess[t]'))]},
 'standard_reverse_ground.i': {'loops': [init('i', 'a'), [f'0 <= i <= {N}', A('0', 'i', f'b[t] == a[{N-1}-t]'), f'assigns i, b[0..{N-1}]'], chk('x', ALL(f'b[t] == a[{N-1}-t]'))]},
 'standard_running-1.i': F({'loops': [init('i', 'a'), [f'0 <= i <= {N}', A('0', 'i', 'b[t] == (a[t] >= 0 ? 1 : 0)'), f'assigns i, b[0..{N-1}]'],
   [f'0 <= i <= {N}', 'f == 0 || f == 1', ALL('b[t] == (a[t] >= 0 ? 1 : 0)'), 'assigns i, f']]}, 'f becomes 0 for negative elements'),
 'standard_running-2.i': {'loops': [init('i', 'a'), [f'0 <= i <= {N}', A('0', 'i', 'b[t] == (a[t] >= 0 ? 1 : 0)'), f'assigns i, b[0..{N-1}]'],
   [f'0 <= i <= {N}', 'f == 1', ALL('b[t] == (a[t] >= 0 ? 1 : 0)'), 'assigns i, f']]},
 'standard_sentinel-2.i': {'loops': [init('i', 'a'), ['0 <= i <= pos', 'a[pos] == marker', 'assigns i']]},
 'standard_seq_init_ground.i': {'loops': [[f'1 <= i <= {N}', '\\forall integer t; 1 <= t < i ==> a[t] == a[t-1] + 1', f'assigns i, a[1..{N-1}]'],
   [f'1 <= x <= {N}', f'\\forall integer t; 1 <= t < {N} ==> a[t] >= a[t-1]', 'assigns x']]},
 'standard_strcmp_ground.i': {'loops': [[f'0 <= i <= {N}', A('0', 'i', 'dst[t] == src[t]'), 'assigns i'], init('i', 'a', 'b'), chk('x', ALL('a[t] == b[t]'))],
   'funcs': {'_strcmp': [f'requires \\valid_read(src + (0..{N-1}))', f'requires \\valid_read(dst + (0..{N-1}))', 'assigns \\nothing', f'ensures \\result == 0 ==> ({ALL("src[t] == dst[t]")})']}},
 'standard_strcpy_ground-1.i': {'loops': [init('j', 'src'), [f'0 <= i <= {N}', A('0', 'i', 'dst[t] == src[t]'), f'assigns i, dst[0..{N-1}]'], ['0 <= x <= i', A('0', 'i', 'dst[t] == src[t]'), 'assigns x']]},
 'standard_strcpy_original-2.i': {'loops': [init('j', 'src'), [f'0 <= i <= {N}', A('0', 'i', 'dst[t] == src[t]'), A('0', 'i', 'src[t] != 0'), f'assigns i, dst[0..{N-1}]'],
   [f'0 <= i <= {N}', A('0', 'i', 'src[t] != 0'), f'\\forall integer t; 0 <= t < {N} ==> (\\forall integer u; 0 <= u <= t ==> src[u] != 0) ==> dst[t] == src[t]', 'assigns i']]},
 'standard_vararg_ground.i': {'loops': [init('i', 'aa'), ['0 <= a', A('0', 'a', 'aa[t] >= 0'), 'assigns a'], ['0 <= x <= a', A('0', 'a', 'aa[t] >= 0'), 'assigns x']]},
 'standard_vector_difference_ground.i': {'loops': [init('i', 'a', 'b'), [f'0 <= i <= {N}', A('0', 'i', 'c[t] == a[t] - b[t]'), f'assigns i, c[0..{N-1}]'], chk('x', ALL('c[t] == a[t] - b[t]'))]},
}
for f in sorted(os.listdir(D)):
    if not f.endswith(('.c', '.i')) or f in SPECS or 'reducer' in f: continue
    text = open(os.path.join(D, f)).read()
    if f.startswith('standard_copy') and 'ground' in f and 'Init' not in f: SPECS[f] = copies(text)
    elif f.startswith('standard_init'):
        exp = int(re.search(r'__VERIFIER_assert\( a\[x\] == (\d+) \)', text).group(1)); SPECS[f] = inits(text, exp)
    elif f.startswith('standard_two_index'):
        s = int(f[-4:-2]); size = int(re.search(r'int b\[(\d+)\]', text).group(1)); SPECS[f] = two_index(s, size)
