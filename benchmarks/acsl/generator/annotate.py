#!/usr/bin/env python3
"""insert ACSL annotations into the copied SV-COMP tasks from spec tables.

usage: annotate.py <folder> [files...]   (reads specs/<folder>.py, defines SPECS)

a spec is a dict with
  'loops': list, one entry per loop (for/while/do) in textual order; each entry is
           None or a list of clauses; a clause is 'loop invariant ...' etc. in full, or
           shorthand: an expression (-> loop invariant), 'assigns ...' / 'variant ...'
           (-> loop assigns / loop variant)
  'funcs': dict name -> list of contract clauses (requires/ensures/assigns in full)
  'decls': dict name -> clauses for an extern declaration (e.g. nondet functions)
  'note':  text for a header line
  'ghost': dict: text -> ACSL text inserted before the first occurrence of text (statement
           level), e.g. assertions or ghost code
the harness contracts (reach_error, __VERIFIER_assert, abort, nondet, assume) are added
automatically. loops: an entry for every loop, the count is checked.
"""
import re, sys, os, importlib.util

# benchmarks/acsl, the parent of this folder; the tasks of sv-benchmarks in SVB (default ~/Projects/sv-benchmarks/c)
ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
SVB = os.environ.get('SVB', os.path.expanduser('~/Projects/sv-benchmarks/c'))

def mask(text):
    """replace comments and string literals by spaces, keeping positions"""
    out = list(text); i = 0; n = len(text)
    while i < n:
        c = text[i]
        if text.startswith('//', i):
            j = text.find('\n', i); j = n if j < 0 else j
            for k in range(i, j): out[k] = ' '
            i = j
        elif text.startswith('/*', i):
            j = text.find('*/', i + 2); j = n if j < 0 else j + 2
            for k in range(i, j): out[k] = ' '
            i = j
        elif c in '"\'':
            j = i + 1
            while j < n and text[j] != c:
                if text[j] == '\\': j += 1
                j += 1
            for k in range(i + 1, min(j, n)): out[k] = ' '
            i = j + 1
        else:
            i += 1
    return ''.join(out)

def match_brace(m, pos):
    depth = 0
    for i in range(pos, len(m)):
        if m[i] == '{': depth += 1
        elif m[i] == '}':
            depth -= 1
            if depth == 0: return i
    raise ValueError('unbalanced braces')

def find_loops(text):
    m = mask(text)
    skip = set(); loops = []
    for mo in re.finditer(r'\b(for|while|do)\b', m):
        p = mo.start()
        if p in skip: continue
        # a label or identifier part? \b handles identifiers; check 'do' not followed by identifier char
        if mo.group(1) == 'do':
            q = p + 2
            while q < len(m) and m[q].isspace(): q += 1
            if q < len(m) and m[q] == '{':
                e = match_brace(m, q)
            else:
                e = q
            w = re.compile(r'\bwhile\b').search(m, e)
            if w: skip.add(w.start())
        loops.append(p)
    return loops

def find_funcs(text):
    """name -> position of the start of the definition line (return type) for function definitions"""
    m = mask(text)
    res = {}
    for mo in re.finditer(r'(?m)^([A-Za-z_][\w \t\*]*?)\b([A-Za-z_]\w*)\s*\(([^;{)]*)\)\s*(?:__attribute__\s*\(\(.*?\)\)\s*)*\{', m):
        res.setdefault(mo.group(2), mo.start())
    return res

def find_decls(text):
    m = mask(text)
    res = {}
    for mo in re.finditer(r'(?m)^(?:extern\s+)?[A-Za-z_][\w \t\*]*?\b([A-Za-z_]\w*)\s*\([^;{)]*\)\s*(?:__attribute__\s*\(\(.*?\)\)\s*)*;', m):
        res.setdefault(mo.group(1), mo.start())
    return res

def clause(s, kind='loop'):
    s = s.strip()
    if s.endswith(';'): s = s[:-1]
    if kind == 'loop':
        if re.match(r'(loop\s+)?(invariant|assigns|variant)\b', s):
            if not s.startswith('loop'): s = 'loop ' + s
            return s + ';'
        return 'loop invariant ' + s + ';'
    return s + ';'

def block(clauses, indent, kind='loop'):
    cs = [clause(c, kind) for c in clauses]
    if len(cs) == 1:
        return f'{indent}/*@ {cs[0]} */\n'
    return f'{indent}/*@ ' + ('\n' + indent + '    ').join(cs) + ' */\n'

def insert_before(text, pos, ann_lines):
    """insert annotation lines before position pos, on their own lines with the indentation of pos"""
    ls = text.rfind('\n', 0, pos) + 1
    prefix = text[ls:pos]
    indent = re.match(r'[ \t]*', prefix).group(0)
    ann = block(ann_lines, indent) if isinstance(ann_lines, list) else ''.join(indent + l + '\n' for l in ann_lines.rstrip('\n').split('\n'))
    if prefix.strip() == '':
        return text[:ls] + ann.replace('\n', '\n', 1) + text[ls:]
    # code before the keyword on the same line: break the line
    return text[:ls] + prefix.rstrip() + '\n' + ann + indent + text[pos:]

HARNESS_FUNCS = {
    'reach_error': ['requires \\false', 'assigns \\nothing'],
    '__VERIFIER_assert': ['requires cond != 0', 'assigns \\nothing'],
    'assume_abort_if_not': ['assigns \\nothing', 'ensures cond != 0'],
    '__VERIFIER_assume': ['assigns \\nothing', 'ensures cond != 0'],
}
HARNESS_DECLS = {
    'abort': ['assigns \\nothing', 'ensures \\false'],
    'exit': ['assigns \\nothing', 'ensures \\false'],
    '__assert_fail': ['assigns \\nothing', 'ensures \\false'],
    '__VERIFIER_assume': ['assigns \\nothing', 'ensures cond != 0'],
}
NONDET = re.compile(r'__VERIFIER_nondet_(\w+)')

def annotate(path, spec):
    text = open(path).read()
    if '/*@' in text or '//@' in text:
        # start over from the upstream copy
        import shutil
        up = path.replace(ROOT, SVB)
        shutil.copy(up, path); text = open(path).read()
    loops = find_loops(text)
    want = spec.get('loops', [])
    if want == 'skip': want = [None] * len(loops)
    if len(loops) != len(want):
        raise ValueError(f'{path}: {len(loops)} loops in the file, {len(want)} in the spec')
    edits = []  # (pos, lines)
    for p, cl in zip(loops, want):
        if cl: edits.append((p, [clause(c, 'loop') for c in cl]))
    funcs = find_funcs(text); decls = find_decls(text)
    fspecs = dict(HARNESS_FUNCS); fspecs.update(spec.get('funcs', {}))
    for name, cl in fspecs.items():
        if name in funcs and cl:
            edits.append((funcs[name], [clause(c, 'func') for c in cl]))
    dspecs = dict(HARNESS_DECLS)
    for name in set(NONDET.findall(text)):
        dspecs['__VERIFIER_nondet_' + name] = ['assigns \\nothing']
    dspecs.update(spec.get('decls', {}))
    for name, cl in dspecs.items():
        if name in decls and cl and not (name in funcs and name in fspecs):
            # a declaration of a function that is also defined gets the contract only once (at the definition)
            if name in funcs: continue
            edits.append((decls[name], [clause(c, 'func') for c in cl]))
    for key, ann in spec.get('ghost', {}).items():
        p = mask(text).find(key)
        if p < 0: raise ValueError(f'{path}: ghost anchor {key!r} not found')
        edits.append((p, ann if ann.endswith('\n') else ann + '\n'))
    # apply from the back so positions stay valid
    for p, ann in sorted(edits, key=lambda e: -e[0]):
        if isinstance(ann, list):
            # function contracts: full clauses already; print as block without the loop prefix
            ls = text.rfind('\n', 0, p) + 1
            indent = re.match(r'[ \t]*', text[ls:p]).group(0)
            cs = ann
            if len(cs) == 1: b = f'{indent}/*@ {cs[0]} */\n'
            else: b = f'{indent}/*@ ' + ('\n' + indent + '    ').join(cs) + ' */\n'
            prefix = text[ls:p]
            if prefix.strip() == '': text = text[:ls] + b + text[ls:]
            else: text = text[:ls] + prefix.rstrip() + '\n' + b + indent + text[p:]
        else:
            text = insert_before(text, p, ann)
    note = spec.get('note')
    header = '// ACSL annotations added by hand (benchmarks/acsl/README.md)' + (': ' + note if note else '') + '\n'
    # after a leading license/comment block, before the first code line
    m = mask(text)
    first = re.search(r'(?m)^\s*[^\s/]', m)
    fp = first.start() if first else 0
    ls = text.rfind('\n', 0, fp) + 1 if fp else 0
    text = text[:ls] + header + text[ls:]
    open(path, 'w').write(text)

def load_specs(folder):
    p = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'specs', folder.replace('-', '_') + '.py')
    s = importlib.util.spec_from_file_location('specs', p); mod = importlib.util.module_from_spec(s); s.loader.exec_module(mod)
    return mod.SPECS


def list_loops(folder, files=None):
    d = os.path.join(ROOT, folder)
    for f in files or sorted(x for x in os.listdir(d) if x.endswith(('.c', '.i'))):
        text = open(os.path.join(d, f)).read()
        ls = find_loops(text)
        print(f'{f}: {len(ls)} loops')
        for p in ls:
            line = text[p:text.find('\n', p)].strip()
            depth = mask(text)[:p].count('{') - mask(text)[:p].count('}')
            print(f'    {"  " * depth}{line[:90]}')

if __name__ == '__main__':
    if sys.argv[1] == '--list':
        list_loops(sys.argv[2], sys.argv[3:]); sys.exit()
    folder = sys.argv[1]
    specs = load_specs(folder)
    files = sys.argv[2:] or sorted(set(specs) | {f for f in os.listdir(os.path.join(ROOT, folder)) if 'reducer' in f and f.endswith('.c')})
    ok = 0; bad = 0
    REDUCER = {'loops': 'skip', 'note': 'an output of a reducer (an unrolled control flow with gotos), only the harness is annotated'}
    for f in files:
        if f not in specs and 'reducer' in f: specs[f] = REDUCER
        if f not in specs: print('no spec:', f); bad += 1; continue
        try:
            annotate(os.path.join(ROOT, folder, f), specs[f]); ok += 1
        except Exception as e:
            print('ERROR', e); bad += 1
    print(f'{folder}: {ok} annotated, {bad} failed')
    missing = [f for f in sorted(os.listdir(os.path.join(ROOT, folder))) if f.endswith(('.c', '.i')) and f not in specs]
    if missing: print('without spec:', len(missing), ' '.join(missing[:10]))
