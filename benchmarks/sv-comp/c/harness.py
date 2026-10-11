# patches the SV-COMP harness into the C programs of this folder, which are printed from the Dafny translations:
# after the leading comments, reach_error, the declarations of the nondet functions used, assume_abort_if_not
# (unless defined), and __VERIFIER_assert, as in sv-benchmarks, unless the file mentions reach_error already;
# in the code, assert(...) becomes __VERIFIER_assert(...), __VERIFIER_assume(...) becomes assume_abort_if_not(...),
# and true and false become 1 and 0, which C has only with stdbool.h, and nothing is included; declarations of
# true and false as variables and assignments to them (in loops-crafted-1/watermelon.c) are dropped
#
#   python3 harness.py [folder]      (default: the folder of this script)
import glob
import os
import re
import sys


# the code of a line, outside comments, with the names of the SV-COMP harness and without true and false
def rename(line):
    if line.lstrip().startswith('//'):
        return line
    line = re.sub(r'\bassert\(', '__VERIFIER_assert(', line)
    line = re.sub(r'\b__VERIFIER_assume\(', 'assume_abort_if_not(', line)
    line = re.sub(r'\btrue\b', '1', line)
    line = re.sub(r'\bfalse\b', '0', line)
    return line


def patch(path):
    original = open(path).read()
    lines = original.split('\n')

    # the leading comments, the command line and the origin of the task
    k = 0
    while k < len(lines) and lines[k].startswith('//'):
        k += 1
    # declarations of true and false as variables, whose values were zero, are dropped, as their uses become 1 and 0
    # and so are the assignments to them, e.g. true = true; of the initial values of globals
    body = [line for line in lines[k:]
            if not re.match(r'^\s*(int|_Bool) (true|false)\s*;\s*$', line) and not re.match(r'^\s*(true|false) = .*;\s*$', line)]
    head, body = lines[:k], [rename(line) for line in body]
    text = '\n'.join(body)

    if 'reach_error' in original:
        if '\n'.join(head + body) != original:
            open(path, 'w').write('\n'.join(head + body))
            return True
        return False

    harness = ['', '// the SV-COMP harness',
               'extern void abort(void);',
               'extern void __assert_fail(const char *, const char *, unsigned int, const char *) '
               '__attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));']
    # the line of reach_error itself, 1-based, as in sv-benchmarks
    line = len(head) + len(harness) + 1
    harness.append('void reach_error() { __assert_fail("0", "%s", %d, "reach_error"); }' % (os.path.basename(path), line))
    if '__VERIFIER_nondet_int' in text:
        harness.append('extern int __VERIFIER_nondet_int(void);')
    if '__VERIFIER_nondet_bool' in text:
        harness.append('extern _Bool __VERIFIER_nondet_bool(void);')
    if 'assume_abort_if_not' in text and 'void assume_abort_if_not' not in text:
        harness += ['void assume_abort_if_not(int cond) {', '  if (!cond) { abort(); }', '}']
    harness += ['void __VERIFIER_assert(int cond) {', '  if (!(cond)) {', '    ERROR: {reach_error(); abort();}', '  }',
                '  return;', '}']

    rest = body if body and body[0] == '' else [''] + body
    open(path, 'w').write('\n'.join(head + harness + rest))
    return True


if __name__ == '__main__':
    folder = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__))
    n = sum(patch(path) for path in sorted(glob.glob(os.path.join(folder, '*', '*.c'))))
    print('patched', n)
