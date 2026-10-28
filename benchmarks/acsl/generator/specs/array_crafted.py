import os, sys
ACSL = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))  # benchmarks/acsl
sys.path.insert(0, os.path.dirname(__file__))
from templates import reducer, zero_sum
D = os.path.join(ACSL, 'array-crafted')
SPECS = {}
for f in sorted(os.listdir(D)):
    if not f.endswith(('.c', '.i')): continue
    text = open(os.path.join(D, f)).read()
    if f.startswith('zero_sum'): SPECS[f] = zero_sum(text, 'const' in f)
    else: SPECS[f] = reducer(text)
