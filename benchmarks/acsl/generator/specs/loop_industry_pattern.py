import os
ACSL = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))  # benchmarks/acsl
SPECS = {'mod3.c': {'loops': [['y == 0 || y == 1', 'y == 0 ==> x % 3 == 0', 'assigns x, y']]}}
for f in os.listdir(os.path.join(ACSL, 'loop-industry-pattern')):
    if f.endswith('.c') and 'reducer' not in f and f != 'mod3.c':
        SPECS[f] = {'loops': 'skip', 'note': 'an industrial program with structs and pointers, only the harness is annotated'}
