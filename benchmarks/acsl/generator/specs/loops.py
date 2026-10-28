A = lambda lo, hi, body: f'\\forall integer t; {lo} <= t < {hi} ==> {body}'
SORTED = lambda hi: f'\\forall integer p, q; 0 <= p < q < {hi} ==> v[p] <= v[q]'
menor = [['0 <= j <= SIZE', A('0', 'j', 'menor <= array[t]'), 'assigns j, menor, array[0..SIZE-1]']]
maior_outer = ['0 <= j <= N_COL', '\\forall integer p, q; 0 <= p < j && 0 <= q < N_LIN ==> matriz[p][q] <= maior', 'assigns j, k, maior, matriz[0..N_COL-1][0..N_LIN-1]']
maior_inner = ['0 <= k <= N_LIN', '\\forall integer p, q; 0 <= p < j && 0 <= q < N_LIN ==> matriz[p][q] <= maior', '\\forall integer q; 0 <= q < k ==> matriz[j][q] <= maior', 'assigns k, maior, matriz[j][0..N_LIN-1]']
isort_bounds = [['0 <= j <= SIZE', 'assigns j, v[0..SIZE-1]'], ['(SIZE == 0 && j == 1) || 1 <= j <= SIZE', 'assigns j, i, key, v[0..SIZE-1]'],
                ['-1 <= i <= j-1', 'assigns i, v[0..j]'], ['(SIZE == 0 && k == 1) || 1 <= k <= SIZE', 'assigns k']]
invert_bounds = lambda M: [['0 <= i <= %s' % M, 'assigns i, str1[0..%s-1]' % M], ['-1 <= i <= %s-1' % M, 'j == %s-1-i' % M, 'assigns i, j, str2[0..%s-1]' % M],
                           ['0 <= i <= %s' % M, 'j == %s-1-i' % M, 'assigns i, j']]
string_loops = [['0 <= i <= 5', 'assigns i, string_A[0..4]'], ['0 <= i <= 5', 'assigns i, string_B[0..4]'],
   ['0 <= nc_A <= 4', A('0', 'nc_A', "string_A[t] != '\\0'"), 'assigns nc_A'], ['0 <= nc_B <= 4', A('0', 'nc_B', "string_B[t] != '\\0'"), 'assigns nc_B'],
   ['0 <= i <= nc_A', '0 <= j <= nc_B', 'j <= i', 'assigns i, j']]
dist = '\\forall integer t; 0 <= t < nodecount ==> 0 <= distance[t] <= INFINITY'
graph = '\\forall integer t; 0 <= t < edgecount ==> 0 <= Dest[t] < nodecount && 0 <= Source[t] < nodecount && Weight[t] >= 0'
lu_main = [['0 <= i <= n', 'n == 5', 'assigns i, j, w, a[0..5][0..5], b[0..5]'], ['0 <= j <= n', '0 <= i <= n', 'assigns j, w, a[i][0..5]']]
lu_dcmp = [['0 <= i <= n'], ['i+1 <= j <= n+1'], ['0 <= k <= i'], ['i+1 <= j <= n+1'], ['0 <= k <= i+1'], ['1 <= i <= n+1'], ['0 <= j <= i'], ['-1 <= i <= n-1'], ['i+1 <= j <= n+1']]
openser = [['-1 <= i <= 8', '0 <= start <= i+1', 'assigns i, j, start, str2[0..1]'], ['0 <= start <= i', 'assigns start'], ['-1 <= j <= i-1', 'assigns j']]
vogal_cnt = """/*@ axiomatic Count {
  logic integer cnt(char *s, integer n) reads s[0..n-1];
  axiom cnt_zero: \\forall char *s; cnt(s, 0) == 0;
  axiom cnt_step: \\forall char *s, integer n; n >= 0 ==>
    cnt(s, n+1) == cnt(s, n) + (s[n] == 'a' || s[n] == 'A' ? 1 : 0);
} */
"""
SPECS = {
 'array-1.c': {'loops': menor},
 'array-2.c': {'loops': menor, 'note': 'expected verdict false (array[0] may equal menor), the invariants are those of array-1'},
 'bubble_sort-2.i': {'loops': 'skip', 'note': 'expected verdict false; a linked-list program with gotos, only the harness is annotated'},
 'compact.c': {'loops': [['0 <= i <= 102400', 'assigns i, array[0..102399]'], ['0 <= i <= 102400', 'assigns i']], 'note': 'expected verdict false, the loop invariants bound i'},
 'count_up_down-1.c': {'loops': [['x + y == n', 'assigns x, y']]},
 'count_up_down-2.c': {'loops': [['x + y == n', 'assigns x, y']], 'note': 'expected verdict false (y == n after the loop), the invariant is that of count_up_down-1'},
 'eureka_01-2.c': {'loops': [
   ['0 <= i <= nodecount', A('0', 'i', '0 <= distance[t] <= INFINITY'), 'assigns i, distance[0..4]'],
   ['0 <= i <= nodecount', dist, graph, 'assigns i, j, x, y, distance[0..4]'],
   ['0 <= j <= edgecount', dist, graph, 'assigns j, x, y, distance[0..4]'],
   ['0 <= i <= edgecount', dist, graph, 'assigns i, x, y'],
   ['0 <= i <= nodecount', dist, 'assigns i']]},
 'eureka_05.i': {'loops': [
   ['0 <= lh <= n', 'assigns lh, rh, i, temp, array[0..n-1]'], ['lh <= rh < n', 'lh+1 <= i <= n', 'assigns i, rh'],
   ['-1 <= i <= 4', '\\forall integer t; i < t < 5 ==> array[t] == t', 'assigns i, array[0..4]'],
   ['0 <= i <= 5', A('0', '5', 'array[t] == t'), 'assigns i']],
   'funcs': {'SelectionSort': ['requires n == 5', 'assigns array[0..n-1]']},
   'note': 'SelectionSort sorts the global array, main checks its local array of the same name'},
 'for_bounded_loop1.c': {'loops': [['0 <= i <= n', 'x == y', 'assigns i, x, y']], 'note': 'expected verdict false (x == y != 0 after the loop)'},
 'for_infinite_loop_1.c': {'loops': [['x == 0', 'assigns i']]},
 'for_infinite_loop_2.c': {'loops': [['x == 0', 'assigns i']]},
 'heavy-1.c': {'loops': [['0 <= i <= 1048576', 'a == 1', 'assigns i, j, k, array[0..1048575]'], ['0 <= j <= 1048576', 'a == 1', 'assigns j, k, array[0..1048575]'], ['0 <= k <= 1048576', 'a == 1', 'assigns k, array[0..1048575]']],
   'note': 'expected verdict false (a == 1 reaches the error), the invariants are those of heavy-2'},
 'heavy-2.c': {'loops': [['0 <= i <= 1048576', 'a == 1', 'assigns i, j, k, array[0..1048575]'], ['0 <= j <= 1048576', 'a == 1', 'assigns j, k, array[0..1048575]'], ['0 <= k <= 1048576', 'a == 1', 'assigns k, array[0..1048575]']]},
 'insertion_sort-1-2.c': {'loops': isort_bounds, 'note': 'expected verdict false (elements are shifted only for i < 2), the loop invariants bound the indices'},
 'insertion_sort-2-2.c': {'loops': [
   ['0 <= j <= SIZE', 'assigns j, v[0..SIZE-1]'],
   ['(SIZE == 0 && j == 1) || 1 <= j <= SIZE', SORTED('j'), 'assigns j, i, key, v[0..SIZE-1]'],
   ['-1 <= i <= j-1', '\\forall integer p, q; 0 <= p < q <= j && p != i+1 && q != i+1 ==> v[p] <= v[q]',
    '\\forall integer p; i+2 <= p <= j ==> v[p] > key', 'assigns i, v[0..j]'],
   ['(SIZE == 0 && k == 1) || 1 <= k <= SIZE', SORTED('SIZE'), 'assigns k']]},
 'invert_string-1.c': {'loops': invert_bounds('MAX'), 'note': 'expected verdict false (str2 is filled with str1[0]), the loop invariants bound the indices'},
 'invert_string-3.c': {'loops': [['0 <= i <= max', 'assigns i, str1[0..max-1]'],
   ['-1 <= i <= max-1', 'j == max-1-i', A('0', 'j', 'str2[t] == str1[max-1-t]'), 'assigns i, j, str2[0..max-1]'],
   ['0 <= i <= max', 'j == max-1-i', A('0', 'max', 'str2[t] == str1[max-1-t]'), 'assigns i, j']]},
 'linear_sea.ch.c': {'loops': [['0 <= j <= n', A('0', 'j', 'a[t] != q'), 'assigns j']],
   'funcs': {'linear_search': ['requires 0 < n && n == SIZE', 'requires \\valid_read(a + (0..n-1))', 'requires \\exists integer t; 0 <= t < n && a[t] == q', 'assigns \\nothing', 'ensures \\result == 1']}},
 'linear_search.c': {'loops': [['0 <= j <= n', A('0', 'j', 'a[t] != q'), 'assigns j']], 'funcs': {'linear_search': ['requires \\valid_read(a + (0..n-1))', 'assigns \\nothing']},
   'note': 'expected verdict false (j == 20 is reset to -1), the loop invariant is that of linear_sea.ch'},
 'lu.cmp.c': {'loops': lu_main + lu_dcmp, 'note': 'the assertion i < 50 follows from the bounds of main\'s loops; the loops of ludcmp carry bounds only'},
 'ludcmp.c': {'loops': lu_main + lu_dcmp, 'note': 'expected verdict false (i == 2 is asserted for every i), the loops carry bounds only'},
 'matrix-1.c': {'loops': [maior_outer, maior_inner]},
 'matrix-2-2.c': {'loops': [maior_outer, maior_inner, ['0 <= j <= N_COL', '\\forall integer p, q; 0 <= p < N_COL && 0 <= q < N_LIN ==> matriz[p][q] <= maior', 'assigns j, k'],
    ['0 <= k <= N_LIN', '\\forall integer p, q; 0 <= p < N_COL && 0 <= q < N_LIN ==> matriz[p][q] <= maior', 'assigns k']],
   'note': 'expected verdict false (the maximum is not strictly below itself), the invariants state <= maior'},
 'n.c11.c': {'loops': [['0 <= len <= 4', 'assigns len, a[0..4]']]},
 'n.c24.i': {'loops': 'skip', 'note': 'expected verdict false; string manipulation with memmove and strlen, only the harness is annotated'},
 'n.c40.c': {'loops': [['i == 0', A('0', '100', 'x[t] == 0'), 'assigns i, y[0..99]']], 'note': 'the global x is zero, so the loop never runs'},
 'nec11.c': {'loops': [['0 <= len <= 4', 'assigns len, a[0..4]']], 'note': 'expected verdict false (len <= 4 always)'},
 'nec20.c': {'loops': [['0 <= i <= n+1', 'j == \\at(j, LoopEntry) + 2*i', 'assigns i, j']], 'note': 'expected verdict false (j may exceed 1024)'},
 'nec40.c': {'loops': [['i == 0', A('0', '100', 'x[t] == 0'), 'assigns i, y[0..99]']], 'note': 'the global x is zero, so the loop never runs'},
 'string-1.i': {'loops': string_loops},
 'string-2.i': {'loops': string_loops, 'note': 'expected verdict false (found is shifted by i), the invariants are those of string-1'},
 'sum01-2.i': {'loops': [['1 <= i && (i <= n+1 || i == 1)', 'sn == 2*(i-1)', 'assigns i, sn']]},
 'sum01_bug02.i': {'loops': [['1 <= i && (i <= n+1 || i == 1)', 'j == 11 - i', '0 <= sn <= 2*(i-1)', 'assigns i, j, sn']], 'note': 'expected verdict false (sn stops growing when i >= j)'},
 'sum03-1.i': {'loops': [['x <= 10 ==> sn == 2*x', 'x > 10 ==> sn == 20', 'assigns sn, x']], 'note': 'expected verdict false (sn stops growing at x == 10)'},
 'sum03-2.i': {'loops': [['sn == (2*x) % 4294967296', 'assigns sn, x']], 'note': 'unsigned arithmetic wraps around, the invariant is stated modulo 2^32'},
 'sum04-1.i': {'loops': [['1 <= i <= 9', 'i <= 4 ==> sn == 2*(i-1)', 'i >= 4 ==> sn == 6', 'assigns i, sn']], 'note': 'expected verdict false (sn == 6 after the loop)'},
 'sum04-2.i': {'loops': [['1 <= i <= 9', 'sn == 2*(i-1)', 'assigns i, sn']]},
 'sum_array-2-2.i': {'loops': [['0 <= i <= M', 'assigns i, A[0..M-1]'], ['0 <= i <= M', 'assigns i, B[0..M-1]'],
   ['0 <= i <= M', A('0', 'i', 'C[t] == A[t] + B[t]'), 'assigns i, C[0..M-1]'], ['0 <= i <= M', A('0', 'M', 'C[t] == A[t] + B[t]'), 'assigns i']]},
 'terminator_01.c': {'loops': [['p == &x', 'assigns x']], 'note': 'expected verdict false (the loop terminates and 0 is asserted)'},
 'terminator_02-2.c': {'loops': [['x < 200', 'z < 200', 'assigns x, z']], 'note': 'the assertion is the negation of the loop condition'},
 'terminator_02-2_abstracted.c': {'loops': []},
 'terminator_03-2.i': {'loops': [['y > 0', 'assigns x']]},
 'terminator_03-2_abstracted.i': {'loops': []},
 'trex01-1.c': {'loops': [['z >= 1', 'assigns z'], ['assigns x, y, z']], 'funcs': {'f': ['assigns \\nothing']}, 'note': 'expected verdict false (z == 1 when k <= 1)'},
 'trex01-2.i': {'loops': [['z >= 1', 'assigns z'], ['assigns x, y, z']], 'funcs': {'f': ['assigns \\nothing']}},
 'trex02-1.c': {'loops': [['assigns x']], 'funcs': {'foo': ['assigns x', 'ensures x == \\old(x) - 1']}},
 'trex02-2.c': {'loops': [['x >= 0 || x == \\at(x, Pre)', 'assigns x']], 'funcs': {'foo': ['assigns x', 'ensures x == \\old(x) - 1']}, 'note': 'expected verdict false (x stays negative)'},
 'trex03-1.c': {'loops': [['d1 == 1 && d2 == 1 && d3 == 1', 'assigns x1, x2, x3, c1, c2']], 'note': 'expected verdict false (only one of x1, x2, x3 needs to be 0)'},
 'trex03-2.c': {'loops': [['d1 == 1 && d2 == 1 && d3 == 1', 'assigns x1, x2, x3, c1, c2']], 'note': 'the assertion is the negation of the loop condition'},
 'trex03-2_abstracted.c': {'loops': []},
 'trex04.c': {'loops': [['d <= 1', 'assigns x']], 'funcs': {'foo': ['assigns \\nothing']}, 'note': 'the assertion is the negation of the loop condition'},
 'trex04_abstracted.c': {'loops': [], 'funcs': {'foo': ['assigns \\nothing']}},
 'veris.c_NetBSD-libc_loop.i': {'loops': [['pathbuf <= p <= pathlim + 1', 'pathlim == tmp', 'assigns p, pathbuf[0..1]']],
   'funcs': {'glob2': ['requires pathlim == tmp', 'requires \\valid(pathbuf + (0..1))', 'requires pathlim == pathbuf + 1', 'assigns pathbuf[0..1]']}},
 'verisec_NetBSD-libc_loop.i': {'loops': [['pathbuf <= p', 'assigns p, pathbuf[0..1]']], 'note': 'expected verdict false (bound is computed in bytes and lies beyond tmp)'},
 'veris.c_OpenSER_cases1_stripFullBoth_arr.i': {'loops': openser + [['0 <= i <= 8', 'assigns i, A[0..7]']],
   'funcs': {'parse_expression_list': ['requires \\valid(str + (0..8))', 'requires str[8] == 0', 'assigns \\nothing']},
   'note': 'the loops carry bounds only; the assertion follows from the check j-start+1 >= 2 before it'},
 'verisec_OpenSER_cases1_stripFullBoth_arr.i': {'loops': openser + [['0 <= i <= 7', 'assigns i, A[0..6]']],
   'funcs': {'parse_expression_list': ['requires \\valid(str + (0..8))', 'requires str[8] == 0', 'assigns \\nothing']},
   'note': 'expected verdict false (no check of the length before the copy), the loops carry bounds only'},
 'veris.c_sendmail_tTflag_arr_one_loop.c': {'loops': [['0 <= i <= 10', 'assigns i, in[0..9]'],
   ['0 <= idx_in <= 10', 'c == in[idx_in]', 'in[10] == 0', 'assigns c, i, j, idx_in']], 'note': 'i is unsigned, the assertion is trivial'},
 'vogal-1.i': {'ghost': {'int main(void)': vogal_cnt}, 'loops': [
   ['0 <= i <= 5', 'assigns i, input_string[0..4]'],
   ['0 <= n_caracter <= 4', A('0', 'n_caracter', "input_string[t] != '\\0'"), 'assigns n_caracter'],
   ['0 <= i <= n_caracter', "vogal_array[0] == 'a' && vogal_array[1] == 'A'", 'cont == cnt(input_string, i)', 'assigns i, j, cont'],
   ['0 <= j <= 2', "vogal_array[0] == 'a' && vogal_array[1] == 'A'", "cont == cnt(input_string, i) + (j >= 1 && input_string[i] == 'a' ? 1 : 0) + (j >= 2 && input_string[i] == 'A' ? 1 : 0)", 'assigns j, cont'],
   ['0 <= i <= n_caracter', A('0', 'n_caracter', "input_string[t] != '\\0'"), "input_string[n_caracter] == '\\0'", "vogal_array[0] == 'a' && vogal_array[1] == 'A'", 'cont_aux == cnt(input_string, i)', 'assigns i, j, cont_aux'],
   ['0 <= j <= 2', "vogal_array[0] == 'a' && vogal_array[1] == 'A'", "cont_aux == cnt(input_string, i) + (j >= 1 && input_string[i] == 'a' ? 1 : 0) + (j >= 2 && input_string[i] == 'A' ? 1 : 0)", 'assigns j, cont_aux']],
   'note': 'the counts are related by the logic function cnt of the axiomatic Count'},
 'vogal-2.i': {'loops': [['0 <= i <= 10', 'assigns i, string_entrada[0..9]'], ['0 <= n_caracter <= 9', 'assigns n_caracter'],
   ['0 <= i <= n_caracter', 'assigns i, j, cont'], ['0 <= j <= 8', 'assigns j, cont'], ['0 <= i <= n_caracter', 'assigns i, j, cont_aux'], ['0 <= j <= 10', 'assigns j, cont_aux']],
   'note': 'expected verdict false (the two loops compare with 8 resp. 10 vowels), the loops carry bounds only'},
 'while_infinite_loop_1.c': {'loops': [['x == 0', 'assigns \\nothing']]},
 'while_infinite_loop_2.c': {'loops': [['x == 0', 'assigns \\nothing']]},
 'while_infinite_loop_3.c': {'loops': [['assigns x'], ['x == 0', 'assigns x']], 'funcs': {'eval': ['assigns x', 'ensures x == 0']}},
 'while_infinite_loop_4.c': {'loops': [['assigns x'], ['0 <= x <= 1', 'assigns x']], 'funcs': {'eval': ['assigns x', 'ensures x == 1']}, 'note': 'expected verdict false (eval sets x to 1)'},
}
