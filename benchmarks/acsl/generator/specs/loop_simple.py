V = 'abcdef'
def nested(k):
    # loop over variable V[j] at depth j: the outer variables are within their bounds, the inner ones are 6
    return [[f'0 <= {V[j]} <= 6'] + [f'{V[l]} == 6' for l in range(j+1, k)] + ['assigns ' + ', '.join(V[j:k])] for j in range(k)]
SPECS = {
 'deep-nested.c': {'loops': [['0 <= a <= uint32_max-1', 'assigns a, b, c, d, e'], ['0 <= b <= uint32_max-1', 'assigns b, c, d, e'],
    ['0 <= c <= uint32_max-1', 'assigns c, d, e'], ['0 <= d <= uint32_max-1', 'assigns d, e'], ['0 <= e <= uint32_max-1', 'assigns e']],
   'note': 'expected verdict false (the error is reached when all counters are uint32_max-2), the loop invariants only bound the counters'},
 'nested_1b.c': {'loops': [['0 <= a <= 6', 'assigns a']], 'note': 'expected verdict false (a == 6 after the loop), the loop invariant bounds a'},
 'nested_1.c': {'loops': nested(1)}, 'nested_2.c': {'loops': nested(2)}, 'nested_3.c': {'loops': nested(3)},
 'nested_4.c': {'loops': nested(4)}, 'nested_5.c': {'loops': nested(5)}, 'nested_6.c': {'loops': nested(6)},
}
