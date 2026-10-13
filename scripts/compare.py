#!/usr/bin/env python3
"""compare.py <baseline.txt> <new.txt>: the verdicts of two result tables of BenchExec (results/*.txt) per task, the
tasks lost and gained, flips between true and false, and the cpu time on the tasks that both solve."""
import re, sys
def load(path):
    rows = {}
    for line in open(path, encoding='utf-8', errors='replace'):
        cols = re.split(r'\s{2,}', line.rstrip('\n'))
        if len(cols) >= 4 and cols[0].endswith('.yml'):
            try: rows[cols[0]] = (cols[1].strip(), float(cols[2]))
            except ValueError: pass
    return rows
base, new = load(sys.argv[1]), load(sys.argv[2])
limit = float(sys.argv[3]) if len(sys.argv) > 3 else 1e9
def kind(s):
    s = s.lower()
    if s.startswith('true'): return 'true'
    if s.startswith('false'): return 'false'
    if s.startswith('timeout'): return 'timeout'
    if s.startswith('error') or s.startswith('out of'): return 'error'
    return 'unknown'
common = sorted(set(base) & set(new))
print(f"tasks: baseline {len(base)}, new {len(new)}, common {len(common)}")
from collections import Counter
print("baseline:", dict(Counter(kind(base[t][0]) for t in common)))
print("new:     ", dict(Counter(kind(new[t][0]) for t in common)))
reg = [(t, base[t], new[t]) for t in common if kind(base[t][0]) in ('true','false') and kind(new[t][0]) not in ('true','false')]
gain = [(t, base[t], new[t]) for t in common if kind(new[t][0]) in ('true','false') and kind(base[t][0]) not in ('true','false')]
flip = [(t, base[t], new[t]) for t in common if kind(base[t][0]) in ('true','false') and kind(new[t][0]) in ('true','false') and kind(base[t][0]) != kind(new[t][0])]
print(f"\nlost ({len(reg)}), of which with baseline cpu <= {limit} s: {sum(1 for t,b,n in reg if b[1] <= limit)}")
for t, b, n in reg:
    print(f"  {t}: {b[0]} {b[1]:.0f}s -> {n[0]} {n[1]:.0f}s")
print(f"\ngained ({len(gain)})")
for t, b, n in gain[:40]:
    print(f"  {t}: {b[0]} {b[1]:.0f}s -> {n[0]} {n[1]:.0f}s")
if len(gain) > 40: print(f"  ... {len(gain)-40} more")
print(f"\nflipped true/false ({len(flip)})")
for t, b, n in flip: print(f"  {t}: {b[0]} -> {n[0]}")
import statistics
same = [t for t in common if kind(base[t][0]) in ('true','false') and kind(new[t][0]) == kind(base[t][0])]
if same:
    print(f"\ncpu time on the {len(same)} tasks solved by both: baseline median {statistics.median(base[t][1] for t in same):.1f} s, new median {statistics.median(new[t][1] for t in same):.1f} s")
