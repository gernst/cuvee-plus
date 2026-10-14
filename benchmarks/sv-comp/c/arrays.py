# sizes the local arrays that the C programs of this folder declare without a size (int a[]; int A[][];), which is
# not valid C, by an unbounded size N that each program assumes to be nonnegative, per function with such arrays:
# - with a parameter N: the declarations stay, assume_abort_if_not(0 <= N) at the start of the function;
# - with a top-level assignment N = ...: the declarations move right after it, after assume_abort_if_not(0 <= N);
# - with N declared but not assigned: the declarations move right after the other declarations, where N is arbitrary;
#   in both cases, if loops over the arrays go beyond N (e.g. up to 2 * N, or i <= N), the arrays get a fresh size M
#   instead, which is assumed to cover these bounds, and N is left alone;
# - without N: a fresh int N = __VERIFIER_nondet_int(), with the declarations moved right before the first top-level
#   statement that uses an array, where N is assumed to cover the bounds B of the loops over the arrays, B <= N for
#   while (i < B ...) and B < N for while (i <= B ...), if their variables do not change afterwards; loops that end
#   at a sentinel, e.g. while (x[i] != 0), have no bound, then only 0 <= N;
# arrays of several dimensions get N for each; assume_abort_if_not is defined in the harness where it is missing,
# so apply harness.py first; functions whose arrays are used before N is assigned are reported and left alone
#
#   python3 arrays.py [folder] [--dry]      (default: the folder of this script)
import collections
import glob
import os
import re
import sys

DECL = re.compile(r'^(\s+)((?:_Bool|int|char|long|unsigned|short)[\w ]*?) (\w+)((?:\[\])+) *;\s*$')
FUNC = re.compile(r'^\S.*\b(\w+)\s*\(([^)]*)\)\s*\{\s*$')
SIZED = ('param', 'own N', 'uninitialized N', 'own N with M', 'uninitialized N with M', 'fresh N', 'fresh N without bounds')


# the functions of a file, as the lines of their header and of their closing brace, and their parameters
def functions(lines):
    i = 0
    while i < len(lines):
        m = FUNC.match(lines[i])
        if m:
            j = i + 1
            while j < len(lines) and lines[j] != '}':
                j += 1
            yield i, j, m.group(2)
            i = j
        i += 1


# the conditions that N covers the bounds of the loops from line p to `end` whose bodies index one of the arrays
# `names`, as far as their variables are not changed from line p on, and with `accesses` also those of the other
# accesses and calls (see below)
def bounds(lines, p, end, names, accesses):
    conditions = []
    for k in range(p, end):
        # the bound is that of the first conjunct, e.g. n of while (j < n && a[j] != q)
        m = re.match(r'^(\s*)while \((\w+) (<|<=) ([^&|)]+?)\s*(&&[^{]*)?\) \{\s*$', lines[k])
        if not m:
            continue
        indent, var, op, bound = len(m.group(1)), m.group(2), m.group(3), m.group(4).strip()
        j = k + 1
        while j < end and not (lines[j].startswith(' ' * indent + '}') and len(lines[j]) - len(lines[j].lstrip()) == indent):
            j += 1
        body = '\n'.join(lines[k + 1:j])
        if not any(re.search(r'\b%s\[' % re.escape(n), body) for n in names):
            continue
        variables = set(re.findall(r'\b[A-Za-z_]\w*\b', bound))
        changed = any(re.search(r'(^|[^=!<>])\b%s\s*(=[^=]|\+\+|--|[-+*/]=)|(\+\+|--)%s\b' % (v, v), line)
                      for v in variables for line in lines[p:end])
        condition = ('%s <= N' if op == '<' else '%s < N') % bound
        if not changed and condition not in conditions:
            conditions.append(condition)
        # the accesses at an offset of the loop variable, e.g. a[2 * i + 1] for i <= N, reach 2 * N + 1, which the
        # size must exceed as well, otherwise the program is not memory safe, which TriCera checks
        last = bound if op == '<=' else '%s - 1' % bound
        if not changed and re.fullmatch(r'\w+', last.strip()):
            for n in names:
                for index in re.findall(r'\b%s\[([^\[\]]+)\]' % re.escape(n), body):
                    if re.search(r'\b%s\b' % re.escape(var), index) and index.strip() != var:
                        reached = re.sub(r'\b%s\b' % re.escape(var), last.strip(), index)
                        if '%s < N' % reached not in conditions:
                            conditions.append('%s < N' % reached)

    # direct accesses a[e] with an index that does not change, e < N, and calls that pass an array, e.g.
    # linear_search(a, SIZE, 3), whose other arguments may bound the accesses of the callee, arg <= N;
    # as lower bounds of a fresh size, too many conditions are harmless
    for k in range(p, end if accesses else p):
        for n in names:
            for index in re.findall(r'\b%s\[([^\[\]]+)\]' % re.escape(n), lines[k]):
                if not unchanged(lines, p, end, index):
                    continue
                condition = '%s < N' % index
                if condition not in conditions:
                    conditions.append(condition)
        for call in re.findall(r'\b\w+\(([^()]*)\)', lines[k]):
            args = [a.strip() for a in call.split(',')]
            if not any(a in names for a in args):
                continue
            for a in args:
                if a in names or not unchanged(lines, p, end, a):
                    continue
                condition = '%s <= N' % a
                if condition not in conditions:
                    conditions.append(condition)
    return conditions


# whether the variables of `expr` are not assigned from line p to `end`
def unchanged(lines, p, end, expr):
    variables = set(re.findall(r'\b[A-Za-z_]\w*\b', expr))
    return not any(re.search(r'(^|[^=!<>])\b%s\s*(=[^=]|\+\+|--|[-+*/]=)|(\+\+|--)%s\b' % (v, v), line)
                   for v in variables for line in lines[p:end])


def size(line):
    return re.sub(r'\[\]', '[N]', line)


def patch(path, write):
    lines = open(path).read().split('\n')
    kinds = []

    # from the last function to the first, such that the line numbers of the others stay valid
    for start, end, params in reversed(list(functions(lines))):
        decls = [k for k in range(start + 1, end) if DECL.match(lines[k])]
        if not decls:
            continue
        names = [DECL.match(lines[k]).group(3) for k in decls]
        body = lines[start + 1:end]

        if re.search(r'\bint N\b', params):
            kind = 'param'
            new = [size(line) if k in decls else line for k, line in enumerate(lines)]
            new.insert(start + 1, '  assume_abort_if_not(0 <= N);')
        else:
            assigns = [k for k in range(start + 1, end) if re.match(r'^  N = .*;\s*$', lines[k])]
            declared = any(re.match(r'^  int N *;\s*$', line) for line in body)
            # the first line after the declarations at the start of the function
            first = start + 1
            while first < end and re.match(r'^  [\w ]+ \w+(\[\w*\])* *;\s*$', lines[first]):
                first += 1

            if assigns or declared:
                p = assigns[0] if assigns else first - 1
                between = [lines[k] for k in range(decls[0] + 1, p + 1) if k not in decls]
                if any(re.search(r'\b%s\b' % re.escape(n), line) for n in names for line in between):
                    kinds.append('used before N')
                    continue
                kind = 'own N' if assigns else 'uninitialized N'
                # bounds of the loops beyond N, e.g. 2 * N or i <= N, need a size M of their own, which leaves N alone
                conditions = bounds(lines, p + 1, end, names, False)
                if all(re.match(r'^N( [-/] \d+)? <=? N$', c) and c != 'N < N' for c in conditions):
                    new = ([line for k, line in enumerate(lines[:p + 1]) if k not in decls]
                           + ['  assume_abort_if_not(0 <= N);'] + [size(lines[k]) for k in decls] + lines[p + 1:])
                else:
                    kind += ' with M'
                    covers = ['0 <= M'] + [re.sub(r' N$', ' M', c) for c in conditions]
                    new = ([line for k, line in enumerate(lines[:p + 1]) if k not in decls]
                           + ['  int M = __VERIFIER_nondet_int();', '  assume_abort_if_not(%s);' % ' && '.join(covers)]
                           + [size(lines[k]).replace('[N]', '[M]') for k in decls] + lines[p + 1:])
            elif any(re.search(r'\bN\b', line) for line in body):
                kinds.append('N otherwise')
                continue
            else:
                # the first top-level statement after the declarations that uses an array
                uses = [k for k in range(decls[-1] + 1, end)
                        if any(re.search(r'\b%s\b' % re.escape(n), lines[k]) for n in names)]
                if not uses:
                    kinds.append('unused arrays')
                    continue
                p = uses[0]
                while p > start + 1 and not re.match(r'^  \S', lines[p]):
                    p -= 1
                conditions = ['0 <= N'] + bounds(lines, p, end, names, True)
                kind = 'fresh N' if len(conditions) > 1 else 'fresh N without bounds'
                new = ([line for k, line in enumerate(lines[:p]) if k not in decls]
                       + ['  int N = __VERIFIER_nondet_int();', '  assume_abort_if_not(%s);' % ' && '.join(conditions)]
                       + [size(lines[k]) for k in decls] + lines[p:])

        lines = new
        kinds.append(kind)

    if write and kinds and all(kind in SIZED for kind in kinds):
        text = '\n'.join(lines)
        if '__VERIFIER_nondet_int()' in text and 'extern int __VERIFIER_nondet_int(void);' not in text:
            text = text.replace('extern void abort(void);\n', 'extern void abort(void);\nextern int __VERIFIER_nondet_int(void);\n', 1)
        if 'void assume_abort_if_not' not in text:
            anchor = 'void __VERIFIER_assert(int cond) {\n'
            text = text.replace(anchor, 'void assume_abort_if_not(int cond) {\n  if (!cond) { abort(); }\n}\n' + anchor, 1)
        open(path, 'w').write(text)
    return kinds


if __name__ == '__main__':
    args = [arg for arg in sys.argv[1:] if arg != '--dry']
    folder = args[0] if args else os.path.dirname(os.path.abspath(__file__))
    write = '--dry' not in sys.argv
    counts = collections.Counter()
    left = []
    for path in sorted(glob.glob(os.path.join(folder, '*', '*.c'))):
        kinds = patch(path, write)
        counts.update(kinds)
        if any(kind not in SIZED for kind in kinds):
            left.append((path, kinds))
    print(dict(counts))
    for path, kinds in left:
        print('left alone:', path, kinds)
