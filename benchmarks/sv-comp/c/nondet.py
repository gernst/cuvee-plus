# initializes the local variables of the C programs of this folder that are declared without a value (int x;
# _Bool b;), whose reads are undefined in C, by the nondet functions of SV-COMP (int x = __VERIFIER_nondet_int();),
# as in the Dafny translations, where such a variable is arbitrary; their declarations are added after reach_error,
# whose line stays the same; globals are left alone, they are zero in C and the translations require so as well
# (requires SIZE == 0); apply harness.py and arrays.py first, since arrays.py looks for N declared without a value
#
#   python3 nondet.py [folder]      (default: the folder of this script)
import glob
import os
import re
import sys

DECL = re.compile(r'^(\s+)(int|_Bool) (\w+) *;\s*$')
NONDET = {'int': '__VERIFIER_nondet_int', '_Bool': '__VERIFIER_nondet_bool'}
EXTERN = {'int': 'extern int __VERIFIER_nondet_int(void);', '_Bool': 'extern _Bool __VERIFIER_nondet_bool(void);'}


def patch(path):
    lines = open(path).read().split('\n')
    types = set()
    for k, line in enumerate(lines):
        m = DECL.match(line)
        if m:
            indent, typ, name = m.groups()
            lines[k] = '%s%s %s = %s();' % (indent, typ, name, NONDET[typ])
            types.add(typ)
    if not types:
        return False
    anchor = next(k for k, line in enumerate(lines) if line.startswith('void reach_error()'))
    missing = [EXTERN[typ] for typ in sorted(types) if EXTERN[typ] not in lines]
    lines[anchor + 1:anchor + 1] = missing
    open(path, 'w').write('\n'.join(lines))
    return True


if __name__ == '__main__':
    folder = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    n = sum(patch(path) for path in sorted(glob.glob(os.path.join(folder, '*', '*.c'))))
    print('patched', n)
