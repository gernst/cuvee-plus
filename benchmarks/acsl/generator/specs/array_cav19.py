A = lambda lo, hi, body: f'\\forall integer t; {lo} <= t < {hi} ==> {body}'
SPECS = {
 'array_doub_access_init_const.c': {'loops': [
   ['0 <= i <= N+1', A('0', '2*i', 'a[t] == 0'), 'assigns i, a[0..2*N+1]'],
   ['0 <= i <= 2*N+1', A('0', '2*N+2', 'a[t] == 0'), 'assigns i']]},
 'array_init_both_ends_multiple_sum.c': {'loops': [
   ['0 <= i <= N', A('0', 'i', 'a[t] == t'), 'assigns i, a[0..N-1]'],
   ['0 <= i <= N', A('0', 'N', 'a[t] == t'), A('N-i', 'N', 'b[t] == N-1-t'), 'assigns i, b[0..N-1]'],
   ['0 <= i <= N', A('0', 'N', 'a[t] == t'), A('0', 'N', 'b[t] == N-1-t'), 'sum == 0', 'assigns i, sum']]},
 'array_init_nondet_vars.c': {'loops': [
   ['1 <= i && (i <= n || i == 1)', A('1', 'i', 'a[t] >= t+2'), 'assigns i, a[1..n-1]'],
   ['1 <= i && (i <= n || i == 1)', A('1', 'n', 'a[t] >= t+2'), 'assigns i']]},
 'array_init_pair_sum_const.c': {'loops': [
   ['0 <= i <= N', A('0', 'i', 'a[t] == 1 && b[t] == 2'), 'assigns i, a[0..N-1], b[0..N-1]'],
   ['0 <= i <= N', A('0', 'N', 'a[t] == 1 && b[t] == 2'), A('0', 'i', 'c[t] == 3'), 'assigns i, c[0..N-1]'],
   ['1 <= i <= N', A('0', 'N', 'c[t] == 3'), 'assigns i']]},
 'array_init_pair_symmetr2.c': {'loops': [
   ['0 <= i <= N', A('0', 'i', 'a[t] > b[t]'), 'assigns i, a[0..N-1], b[0..N-1]'],
   ['0 <= i <= N', A('0', 'N', 'a[t] > b[t]'), A('0', 'i', 'c[t] == a[t] - b[t]'), 'assigns i, c[0..N-1]'],
   ['1 <= i <= N', A('0', 'N', 'c[t] > 0'), 'assigns i']]},
 'array_init_pair_symmetr.c': {'loops': [
   ['0 <= i <= N', A('0', 'i', 'b[t] == -a[t]'), 'assigns i, a[0..N-1], b[0..N-1]'],
   ['0 <= i <= N', A('0', 'N', 'b[t] == -a[t]'), A('0', 'i', 'c[t] == 0'), 'assigns i, c[0..N-1]'],
   ['1 <= i <= N', A('0', 'N', 'c[t] == 0'), 'assigns i']]},
 'array_init_var_plus_ind2.c': {'loops': [
   ['0 <= i <= N', '2*j == i*(i-1)', 'k == -j', A('0', 'i', '2*a[t] == t*(t-1)'), 'assigns i, j, k, a[0..N-1]'],
   ['1 <= l && (l <= i || l == 1)', 'k <= 0', A('0', 'i', 'a[t] >= 0'), 'assigns l']]},
 'array_init_var_plus_ind3.c': {'loops': [
   ['0 <= i <= N', '2*j == -(i*(i-1))', A('0', 'i', '2*a[t] == -(t*(t-1))'), 'assigns i, j, a[0..N-1]'],
   ['4 <= k && (k <= i || k == 4)', '\\forall integer t; 0 <= t < i ==> a[t] <= 0', 'assigns k']]},
 'array_init_var_plus_ind.c': {'loops': [
   ['0 <= i <= N', '2*j == i*(i-1)', A('0', 'i', '2*a[t] == t*(t-1)'), 'assigns i, j, a[0..N-1]'],
   ['1 <= k && (k <= i || k == 1)', '\\forall integer t; 0 <= t < i ==> a[t] >= 0', 'assigns k']]},
 'array_min_and_copy_shift_sum_add.c': {'loops': [
   ['0 <= i && (i <= N || i == 0)', A('0', 'i', 'j <= a[t]'), 'assigns i, j'],
   ['0 <= i && (i <= N || i == 0)', A('0', 'N', 'j <= a[t]'), A('0', 'i', 'b[t] == a[t] - j'), 'assigns i, b[0..N-1]'],
   ['0 <= i && (i <= N || i == 0)', A('0', 'N', 'b[t] >= 0'), 'k >= 0', 'assigns i, k']]},
 'array_tiling_poly6.c': {'loops': [
   ['0 <= i <= S', A('0', 'i', 'a[t] == (t-1)*(t+1)'), 'assigns i, a[0..S-1]'],
   ['0 <= i <= S', A('0', 'i', 'a[t] == -1'), A('i', 'S', 'a[t] == (t-1)*(t+1)'), 'assigns i, a[0..S-1]'],
   ['0 <= i <= S', A('0', 'S', 'a[t] == -1'), 'assigns i']]},
 'array_tiling_tcpy.c': {'loops': [
   ['0 <= i <= S', A('0', 'i', 'acopy[t] == a[t]'), A('2*S-i', '2*S', 'acopy[t] == a[t]'), 'assigns i, acopy[0..2*S-1]'],
   ['0 <= i <= 2*S', A('0', '2*S', 'acopy[t] == a[t]'), 'assigns i']]},
 'array_tripl_access_init_const.c': {'loops': [
   ['0 <= i <= N+1', A('0', '3*i', 'a[t] == 0'), 'assigns i, a[0..3*N+2]'],
   ['0 <= i <= 3*N+1', A('0', '3*N+3', 'a[t] == 0'), 'assigns i']]},
}
