#!/usr/bin/env python3
"""missing.py <logfiles.zip> <tasks>: for each task of the file <tasks> (paths of .yml files, one per line), the rules
that a run of -rules (its :used lists in the zipped log files of BenchExec) applied and that the current lemma database
(resources/cuvee/teq.dfy and the modules of resources/cuvee/teq) no longer has, e.g. to find the rules
that a migration of a module dropped; names of the C prelude (uint, truth, ...) are listed as well."""
import re, sys, zipfile, glob
names = set()
for p in ['resources/cuvee/teq.dfy'] + glob.glob('resources/cuvee/teq/*.dfy'):
    names |= set(re.findall(r'lemma (?:\{:[^}]*\} )*(\w+)', open(p).read()))
z = zipfile.ZipFile(sys.argv[1]); files = z.namelist()
from collections import Counter
total = Counter()
for t in open(sys.argv[2]).read().split():
    base = t.split('/')[-1]
    log = [f for f in files if f.endswith('.' + base + '.log')]
    if not log: print(t, 'no log'); continue
    text = z.read(log[0]).decode(errors='replace')
    used = re.findall(r'\((\w+) (\d+)\)', text[text.find(':used'):]) if ':used' in text else []
    miss = sorted({u for u, _ in used if u not in names})
    total.update(miss)
    print(t, 'missing:', ' '.join(miss) or '-')
print('\ncounts:', total.most_common())
