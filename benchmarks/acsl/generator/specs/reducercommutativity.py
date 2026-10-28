import os, sys
ACSL = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))  # benchmarks/acsl
sys.path.insert(0, os.path.dirname(__file__))
from templates import reducer
D = os.path.join(ACSL, 'reducercommutativity')
SPECS = {}
for f in sorted(os.listdir(D)):
    if f.endswith('.i'):
        SPECS[f] = reducer(open(os.path.join(D, f)).read(), false=f.startswith('rangesum'))
