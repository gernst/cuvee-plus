#!/usr/bin/env python3
"""The rows of Cuvée in the table of doc/paper/cuvee.tex, from the newest runs of the current version with 15 min.

On the valid tasks of SV-COMP 2026 (the void ones, category missing in the official results, left out): correct true
and false, wrong, the safe tasks that Cuvée proves in either configuration and that no official tool reports as true,
confirmed or not ("unique true"), and the score. Prints the rows as LaTeX and the result files, for
doc/paper/README.md.
"""

from pathlib import Path

import common
import experiments

CURRENT = "0.46."
CONFIGURATIONS = ["cuvee", "cuvee-fallback"]
OFFICIAL = ["symbiotic", "aise", "uautomizer", "cpachecker", "korn"]


def main():
    parser = common.arguments(__doc__.splitlines()[0])
    args = parser.parse_args()
    need = experiments.Need(("-verify",), version=CURRENT)
    official = common.collect(OFFICIAL, common.CATEGORIES, args.official, quiet=True)
    for name in common.CATEGORIES:
        runs = [run for results in official.values() if name in results for run in results[name].runs]
        valid = {run.task for run in runs if run.result != "missing"}
        proved_elsewhere = {run.task for run in runs if run.verdict == "true"}
        ours = {tool: experiments.find(tool, name, need, args.results) for tool in CONFIGURATIONS}
        print(f"% {name}: {len(valid)} valid tasks")
        for tool, results in ours.items():
            print(f"%   {tool}: {results.path.name if results else 'missing'} ({results.version if results else '-'})")
        rows = {"correct true": [], "correct false": [], "wrong": [], "score": []}
        unique = set()
        for tool, results in ours.items():
            if results is None:
                for row in rows.values():
                    row.append("--")
                continue
            counted = [run for run in results.runs if run.task in valid]
            rows["correct true"].append(sum(run.outcome == ("correct", "true") for run in counted))
            rows["correct false"].append(sum(run.outcome == ("correct", "false") for run in counted))
            rows["wrong"].append(sum(run.outcome is not None and run.outcome[0] == "wrong" for run in counted))
            rows["score"].append(sum(run.score for run in counted))
            unique |= {run.task for run in counted if run.outcome == ("correct", "true")} - proved_elsewhere
        for row, values in rows.items():
            print(rf"\quad {row} & " + " & ".join(str(value) for value in values) + r" \\")
        print(rf"\quad unique true & \multicolumn{{2}}{{c}}{{{len(unique)}}} \\")


if __name__ == "__main__":
    main()
