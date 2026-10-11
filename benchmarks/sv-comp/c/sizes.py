# bounds the sizes N and M that arrays.py gives to the local arrays of the C programs of this folder from above,
# such that the arrays of a function together take less than 2^31 bytes (PTRDIFF_MAX of ILP32): without, int a[N]
# wraps around the 32-bit address space for N >= 2^30, int A[N][N] for N >= 2^15, and separate arrays overlap, which
# makes reach_error reachable (e.g. UAutomizer places A, B, C of loops/sum_array-2-2 at the same address); the bound
# is the largest limit of a datatype, 2^k - 1 (e.g. 2^15 - 1 of short, 2^16 - 1 of unsigned short), below the largest
# such value, appended to the assumption 0 <= N of arrays.py; files with a bound already stay alone
#
#   python3 sizes.py [folder]      (default: the folder of this script)
import collections
import glob
import os
import re
import sys

LIMIT = 2 ** 31 - 1
SIZEOF = {'int': 4, '_Bool': 1}
DECL = re.compile(r'^\s+(int|_Bool) \w+((?:\[(N|M)\])+) *;\s*$')
ASSUME = re.compile(r'^(\s*assume_abort_if_not\()(.*)(\);\s*)$')


# the largest 2^k - 1 with sum of sizeof * x^d over the arrays at most LIMIT
def largest(arrays):
    lo, hi = 0, LIMIT
    while lo < hi:
        x = (lo + hi + 1) // 2
        if sum(size * x ** d for size, d in arrays) <= LIMIT:
            lo = x
        else:
            hi = x - 1
    return 2 ** (lo + 1).bit_length() // 2 - 1


def patch(path):
    lines = open(path).read().split('\n')
    # the arrays by the line of the assumption 0 <= X that precedes them, X the size
    arrays = collections.defaultdict(list)
    for k, line in enumerate(lines):
        m = DECL.match(line)
        if not m:
            continue
        x = m.group(3)
        a = next(j for j in range(k - 1, -1, -1)
                 if ASSUME.match(lines[j]) and re.search(r'\b0 <= %s\b' % x, lines[j]))
        arrays[(a, x)].append((SIZEOF[m.group(1)], m.group(2).count('[')))
    changed = False
    for (a, x), found in arrays.items():
        if re.search(r'\b%s <= \d+' % x, lines[a]):
            continue
        m = ASSUME.match(lines[a])
        lines[a] = '%s%s && %s <= %d%s' % (m.group(1), m.group(2), x, largest(found), m.group(3))
        changed = True
    if changed:
        open(path, 'w').write('\n'.join(lines))
    return changed


if __name__ == '__main__':
    folder = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    n = sum(patch(path) for path in sorted(glob.glob(os.path.join(folder, '*', '*.c'))))
    print('patched', n)
