A = lambda lo, hi, body: f'\\forall integer t; {lo} <= t < {hi} ==> {body}'
SPECS = {
 'simple_array_index_value_1-1.i': {'loops': [
   ['0 <= index <= 1000', A('0', 'index', 'array[t] == t % 2'), 'assigns index, array[0..999]'],
   ['0 <= index <= 1000', A('0', '1000', 'array[t] == t % 2'), 'assigns index']]},
 'simple_array_index_value_1-2.i': {'loops': [['tmp < 10000', 'assigns index, tmp, array[0..9999]']],
   'note': 'expected verdict false (array[0] is uninitialized when the loop exits at once), the loop invariant bounds tmp'},
 'simple_array_index_value_2.i': {'loops': [
   ['0 <= index <= 10000', A('0', 'index', 'array[t] > t'), 'assigns index, array[0..9999]'],
   ['0 <= index <= 10000', A('0', '10000', 'array[t] > t'), 'assigns index']]},
 'simple_array_index_value_3.i': {'loops': [
   ['0 <= index <= 10000', 'tmp == 2*index', A('0', 'index', 'array[t] == 2*t'), 'assigns index, tmp, array[0..9999]'],
   ['0 <= index <= 10000', A('0', '10000', 'array[t] == 2*t'), 'assigns index']]},
 'simple_array_index_value_4.i': {'loops': [
   ['0 <= i <= 100000', 'assigns i, array[0..99999]'],
   ['index1 <= index2 + 1', 'index1 < 100000', 'index2 < 100000',
    '\\forall integer t; \\at(index1,LoopEntry) <= t < index1 ==> array[t] == array[index1 + index2 - t]',
    'assigns index1, index2, loop_entered'],
   ['index2 <= index1 + 1', 'index1 < 100000', 'index2 < 100000',
    '\\forall integer t; index2 <= t <= index1 ==> array[t] == array[index1 + index2 - t]',
    'assigns index1, index2']]},
 'simple_vardep_1.c': {'loops': [['j == 2*i', 'k == 3*i', 'assigns i, j, k']]},
 'simple_vardep_2.c': {'loops': [['j == 2*i', 'k == 3*i', 'assigns i, j, k']]},
}
