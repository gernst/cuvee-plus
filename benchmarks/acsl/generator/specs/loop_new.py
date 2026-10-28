SPECS = {
 'count_by_1.i': {'loops': [['0 <= i <= 1000000', 'assigns i']]},
 'count_by_1_variant.i': {'loops': [['0 <= i <= 1000000', 'assigns i']]},
 'count_by_2.i': {'loops': [['0 <= i <= 1000000', 'i % 2 == 0', 'assigns i']]},
 'count_by_k.i': {'loops': [['0 <= i <= 1000000*k', '\\exists integer q; 0 <= q && i == q*k', 'assigns i']]},
 'count_by_nondet.i': {'loops': [['0 <= k <= i', 'k <= 1000000', 'assigns i, k']]},
 'gauss_sum.i': {'loops': [['1 <= i <= n+1', '2*sum == i*(i-1)', 'assigns i, sum']]},
 'half.i': {'loops': [['0 <= i && (i <= 2*k || i == 0)', '2*n == i + i % 2', 'assigns i, n']]},
 'nested-1.i': {'loops': [['0 <= i <= n', 'k == i*m', 'assigns i, j, k'], ['0 <= j <= m', 'k == i*m + j', 'assigns j, k']]},
}
