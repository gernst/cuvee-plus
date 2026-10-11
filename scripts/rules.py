"""Frequencies of the rewrite rules that Cuvée applies in the proved tasks (option -rules).

For each benchmark of Cuvée and category, the most recent results (see common.latest) and their logs: a goal that
simplifies to true is reported on stderr as "used by goal 1, which simplified to true: name count, ...", a goal that
remains carries attributes :used (name count). Only the tasks whose verdict true is correct count, since the logs of
the others are incomplete, e.g. those stopped by the time limit. Per rule: the tasks that use it and its
applications, per category and in total, written as CSV and as a LaTeX table; the lemmas of teq.dfy that no proved
task uses are listed. The counts are upper bounds, since rewrites in subterms that are dropped later count as well.
"""

import collections
import csv
import re
import sys
import zipfile
from pathlib import Path

import common

TEQ = common.SCRIPTS.parent / "resources" / "cuvee" / "teq.dfy"

# "used by goal 1, which simplified to true: counter_def 1, stores 1" (or "none")
CLOSED = re.compile(r"^used by .+?, which simplified to true: (.*)$", re.M)
# :used (name count), also across lines and as {:used (name count)} in Dafny
USED = re.compile(r":used \(\s*([^\s()]+)\s+(\d+)\s*\)")


def logs(results: common.Results) -> dict[str, str]:
    """The logs of the runs of `results` by the file names of their tasks, e.g. simple_3-1.yml."""
    stem = results.path.name.split(".results.", 1)[0]
    found = {}
    archive = results.path.with_name(stem + ".logfiles.zip")
    folder = results.path.with_name(stem + ".logfiles")
    if archive.is_file():
        with zipfile.ZipFile(archive) as zip:
            for name in zip.namelist():
                if name.endswith(".yml.log"):
                    found[name.rsplit("/", 1)[-1].split(".", 1)[1][: -len(".log")]] = zip.read(name).decode(errors="replace")
    elif folder.is_dir():
        for path in folder.glob("*.yml.log"):
            found[path.name.split(".", 1)[1][: -len(".log")]] = path.read_text(errors="replace")
    return found


def counts(log: str) -> collections.Counter:
    """The applications of each rule in the log of one run, summed over its goals."""
    used = collections.Counter()
    for line in CLOSED.findall(log):
        if line.strip() == "none":
            continue
        for item in line.split(", "):
            name, _, n = item.rpartition(" ")
            if name and n.isdigit():
                used[name] += int(n)
    for name, n in USED.findall(" ".join(log.split())):
        used[name] += int(n)
    return used


def lemmas(path: Path = TEQ) -> list[str]:
    """The names of the lemmas of teq.dfy, in their order."""
    text = path.read_text() if path.is_file() else ""
    return re.findall(r"^lemma\s+(?:\{:[^}]*\}\s*)*(\w+)", text, re.M)


def main():
    parser = common.arguments(__doc__.splitlines()[0])
    parser.set_defaults(tools=["cuvee", "cuvee-fallback"])
    parser.add_argument("--top", type=int, default=0, help="the number of rules in the LaTeX table (default: 0, all)")
    args = parser.parse_args()

    collected = common.collect(args.tools, args.categories, args.results)
    if not collected:
        sys.exit("no results found")

    # per (benchmark, category): the tasks and the applications of each rule, and the number of proved tasks
    tasks: dict[tuple[str, str], collections.Counter] = {}
    applications: dict[tuple[str, str], collections.Counter] = {}
    proved: dict[tuple[str, str], int] = {}
    for tool, categories in collected.items():
        for name, results in categories.items():
            found = logs(results)
            key = (tool, name)
            tasks[key], applications[key], proved[key] = collections.Counter(), collections.Counter(), 0
            for run in results.runs:
                if run.outcome != ("correct", "true"):
                    continue
                proved[key] += 1
                log = found.get(Path(run.task).name)
                if log is None:
                    print(f"no log of {run.task} in {results.path.name}", file=sys.stderr)
                    continue
                used = counts(log)
                tasks[key].update(used.keys())
                applications[key].update(used)

    args.output.mkdir(parents=True, exist_ok=True)

    # one row per benchmark, category, and rule, and the totals over the categories
    rows = []
    for tool in collected:
        keys = [key for key in tasks if key[0] == tool]
        for key in keys + [(tool, "Total")]:
            if key[1] == "Total":
                used_tasks = sum((tasks[k] for k in keys), collections.Counter())
                used_applications = sum((applications[k] for k in keys), collections.Counter())
                total = sum(proved[k] for k in keys)
            else:
                used_tasks, used_applications, total = tasks[key], applications[key], proved[key]
            for rule, n in sorted(used_tasks.items(), key=lambda item: (-item[1], item[0])):
                rows.append((tool, key[1], rule, n, used_applications[rule], total))

    with open(args.output / "rules.csv", "w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(["benchmark", "category", "rule", "tasks", "applications", "proved tasks"])
        writer.writerows(rows)

    # the rules of each benchmark over all categories, by the number of tasks that use them, all by default,
    # as a longtable, which breaks across pages (\usepackage{longtable})
    lines = [r"\begin{longtable}{l" + "rr" * len(collected) + "}", r"\toprule"]
    labels = common.labels(collected)
    lines.append("rule & " + " & ".join(rf"\multicolumn{{2}}{{c}}{{{labels[tool]}}}" for tool in collected) + r" \\")
    lines.append(" & " + " & ".join(["tasks & applications"] * len(collected)) + r" \\")
    lines += [r"\midrule", r"\endhead"]
    totals = {tool: {row[2]: (row[3], row[4]) for row in rows if row[0] == tool and row[1] == "Total"} for tool in collected}
    ranking = collections.Counter()
    for tool in collected:
        for rule, (n, _) in totals[tool].items():
            ranking[rule] = max(ranking[rule], n)
    ranked = sorted(ranking.items(), key=lambda item: (-item[1], item[0]))
    for rule, _ in ranked[: args.top] if args.top > 0 else ranked:
        cells = []
        for tool in collected:
            n, m = totals[tool].get(rule, (0, 0))
            cells += [str(n), str(m)]
        lines.append(r"\texttt{" + rule.replace("_", r"\_") + "} & " + " & ".join(cells) + r" \\")
    lines += [r"\bottomrule", r"\end{longtable}", ""]
    (args.output / "rules.tex").write_text("\n".join(lines))

    # the lemmas of teq.dfy that no proved task of any benchmark uses
    used = set(ranking)
    unused = [name for name in lemmas() if name not in used]
    (args.output / "rules-unused.txt").write_text("".join(name + "\n" for name in unused))

    for tool in collected:
        print(f"{labels[tool]}: {sum(proved[k] for k in proved if k[0] == tool)} proved tasks, {len(totals[tool])} rules used")
    print(f"{len(unused)} of {len(lemmas())} lemmas of teq.dfy unused")
    print(args.output / "rules.csv")
    print(args.output / "rules.tex")


if __name__ == "__main__":
    main()
