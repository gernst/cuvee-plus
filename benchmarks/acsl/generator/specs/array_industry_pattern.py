N = 100000
A = lambda lo, hi, body: f'\\forall integer t; {lo} <= t < {hi} ==> {body}'
ALL = lambda body: A('0', N, body)
B = f'0 <= i <= {N}'
F = lambda spec, why: dict(spec, note='expected verdict false (' + why + ')')
ok = lambda arr: f'({arr} != \\null && {arr}->n == 0) ==> {arr}->p != \\null'
distinct = lambda hi: f'\\forall integer p, q; 0 <= p < q < {hi} ==> set[p] != set[q]'
SPECS = {
 'array_assert_loop_dep.i': F({'loops': [[B, A('0', 'i', 'a[t] == 10'), f'assigns i, a[0..{N-1}]'], [B, f'assigns i, a[0..{N-1}]']]}, 'a[i+1] is set to 20 before it is checked'),
 'array_monotonic.i': {'loops': [[B, 'i % 2 == 0', A('0', 'i', '(t % 2 == 0 && a[t] == 10) ==> b[t] == 20'), f'assigns i, b[0..{N-1}]'],
   [B, 'i % 2 == 0', ALL('(t % 2 == 0 && a[t] == 10) ==> b[t] == 20'), 'assigns i']]},
 'array_mul_init.i': {'loops': [[B, A('0', 'i', 'a[t] == t && b[t] == t'), f'assigns i, a[0..{N-1}], b[0..{N-1}]'],
   [B, A('0', 'i', 'a[t] == b[t] || b[t] == a[t] * a[t]'), A('i', N, 'a[t] == b[t]'), f'assigns i, a[0..{N-1}], b[0..{N-1}]'], [B, ALL('a[t] == b[t] || b[t] == a[t] * a[t]'), 'assigns i']]},
 'array_of_struct_break.i': {'loops': [[B, A('0', 'i', 's[t].n == 10'), f'assigns i, s[0..{N-1}].n'], [B, f'c <= 5 ==> ({ALL("s[t].n == 10")})', 'assigns i']]},
 'array_of_struct_loop_dep.i': F({'loops': [[B, A('0', 'i', 'a[t].n == 10'), f'assigns i, a[0..{N-1}].n'], [B, f'assigns i, a[0..{N-1}].n']]}, 'a[i+1].n is set to 20 before it is checked'),
 'array_of_struct_ptr_cond_init.i': {'loops': [[B, A('0', 'i', '\\valid(a[t]) && (a[t]->n == 1 ==> a[t]->p != \\null)'), f'assigns i, a[0..{N-1}]'],
   [B, ALL('\\valid(a[t]) && (a[t]->n == 1 ==> a[t]->p != \\null)'), 'assigns i']], 'funcs': {'user_read': ['assigns \\nothing']}},
 'array_of_struct_ptr_flag_init.i': {'loops': [['0 <= i <= size', A('0', 'i', 'a[t].n != \\null'), 'assigns i, a[0..size-1].n'],
   [B, 'flag == 0 || flag == 1', 'i > 0 ==> flag == 1', ALL('a[t].n != \\null'), 'assigns i, flag'], [B, 'flag == 1', 'assigns i']],
   'funcs': {'init': ['requires size >= 0', 'requires \\valid(a + (0..size-1))', 'assigns a[0..size-1].n', 'ensures \\forall integer t; 0 <= t < size ==> a[t].n != \\null']}},
 'array_of_struct_ptr_monotonic.i': {'loops': [[B, 'i % 2 == 0', A('0', 'i', 't % 2 == 0 ==> \\valid(a[t]) && (a[t]->t == 10 ==> a[t]->p1 != \\null)'), f'assigns i, a[0..{N-1}]'],
   [B, 'i % 2 == 0', ALL('t % 2 == 0 ==> \\valid(a[t]) && (a[t]->t == 10 ==> a[t]->p1 != \\null)'), 'assigns i']]},
 'array_of_struct_ptr_mul_init.i': {'loops': [[B, A('0', 'i', 'a[t].p == a[t].q'), f'assigns i, a[0..{N-1}]'],
   [B, A('0', 'i', 'a[t].p == a[t].q || a[t].q == a[t].p * a[t].p'), A('i', N, 'a[t].p == a[t].q'), f'assigns i, a[0..{N-1}]'], [B, ALL('a[t].p == a[t].q || a[t].q == a[t].p * a[t].p'), 'assigns i']]},
 'array_of_struct_single_elem_init.i': {'loops': [[B, A('0', 'i', 'a[t].n == 0 ==> a[t].p == 10'), f'assigns i, a[0..{N-1}]'], [B, ALL('(t != 3 && a[t].n == 0) ==> a[t].p == 10'), 'assigns i']]},
 'array_ptr_partial_init.i': {'loops': [[B, A('0', 'i', 'a[t] == \\null'), f'assigns i, a[0..{N-1}]'], [f'0 <= i <= {N//2}', A('0', 'i', 'a[t] != \\null'), f'assigns i, a[0..{N//2-1}]'],
   [f'0 <= i <= {N//2}', A('0', N//2, 'a[t] != \\null'), 'assigns i']]},
 'array_ptr_single_elem_init-1.i': {'loops': [[B, A('0', 'i', ok('a[t]')), f'assigns i, a[0..{N-1}]'], [B, ALL(f't != 3 ==> ({ok("a[t]")})'), 'assigns i']]},
 'array_ptr_single_elem_init-2.i': F({'loops': [[B, A('0', 'i', 'a[t] == 0 || a[t] == 1'), f'assigns i, a[0..{N-1}], b[0..{N-1}], c[0..{N-1}]'], [B, 'a[15000] == 1', 'assigns i']]}, 'a[15000] is 1'),
 'array_range_init.i': F({'loops': [[B, A('0', 'i', 'a[t] == (t <= 10000 ? 10 : 0)'), f'assigns i, a[0..{N-1}]'], [B, ALL('a[t] == (t <= 10000 ? 10 : 0)'), 'assigns i']]}, 'the elements above 10000 are 0'),
 'array_shadowinit.i': {'loops': [['0 <= i <= N', 'k == i', A('0', 'i', 'a[t] == t'), 'assigns i, k, a[0..N-1]'], ['0 <= i <= N', A('0', 'N', 'a[t] == t'), 'assigns i']]},
 'array_single_elem_init.i': F({'loops': [[B, A('0', 'i', '(a[t] == 0 || a[t] == 1) && (a[t] != 0 ==> b[t] == t % 2 && c[t] == (t % 2 == 0 ? 0 : 1))'), f'assigns i, a[0..{N-1}], b[0..{N-1}], c[0..{N-1}]'],
   [B, 'assigns i']]}, 'c[15000] is not written when q != 0'),
 'check_removal_from_set_after_insertion.c': F({'loops': [
   ['0 <= i <= size', A('0', 'i', 'set[t] != value'), 'assigns i'],
   ['0 <= i <= SIZE', 'assigns i, values[0..SIZE-1]'],
   ['0 <= v <= SIZE', '0 <= n <= v', distinct('n'), 'assigns v, n, set[0..SIZE-1]'],
   ['0 <= i <= SIZE', 'found == 0 || found == 1', f'found == 0 ==> ({A("0", "i", "set[t] != element")})', f'found == 1 ==> (0 <= pos < i && set[pos] == element && ({A("0", "pos", "set[t] != element")}))', 'assigns i, found, pos'],
   ['pos <= i <= SIZE - 1', '0 <= pos', A('0', 'pos', 'set[t] != element'), 'assigns i, set[pos..SIZE-1]'],
   ['0 <= i <= SIZE - 1', A('0', 'pos', 'set[t] != element'), 'assigns i']],
   'funcs': {'insert': ['requires 0 <= size < SIZE', 'requires \\valid(set + size)', 'assigns set[size]', 'ensures \\result == size + 1', 'ensures set[size] == value'],
             'elem_exists': ['requires 0 <= size <= SIZE', 'requires \\valid_read(set + (0..size-1))', 'assigns \\nothing', 'ensures (\\result == 1) <==> (\\exists integer t; 0 <= t < size && set[t] == value)']}},
   'the elements beyond n are arbitrary and may equal the removed element'),
}
