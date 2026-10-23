"""Frequencies of the rewrite rules that Cuvée applies in the proved tasks (option -rules).

For each benchmark of Cuvée and category, the most recent results (see common.latest) and their logs: each
-prove (formerly -simplify) reports the rules that it applies to an assertion as (set-info :used ((name count) ...)), which the counts
of several -prove add up; logs before 0.41.2 report a goal that simplifies to true on stderr as "used by goal 1,
which simplified to true: name count, ...", and a goal that remains carries attributes :used (name count). Only the tasks whose verdict true is correct count, since the logs of
the others are incomplete, e.g. those stopped by the time limit. Per rule: the tasks that use it and its
applications, per category and in total, written as CSV, as a LaTeX table, and as a bar chart of the number of tasks
per rule (rules-frequency.pdf), compiled to rules.pdf; the lemmas of teq.dfy that no proved task uses are listed. The
counts are upper bounds, since rewrites in subterms that are dropped later count as well.
"""

import collections
import csv
import re
import sys
import zipfile
from pathlib import Path

import common
from table import pdflatex

TEQ = common.SCRIPTS.parent / "resources" / "cuvee" / "teq.dfy"
# the migrated modules of the database that the benchmark definitions include (-include teq:<module>)
MODULES = ["aggregation", "arithmetic", "arrays", "counters", "search", "sorted", "strides", "unsigned"]
DATABASE = [TEQ] + [TEQ.parent / "teq" / f"{name}.dfy" for name in MODULES]

# the document of the statistics, compiled to rules.pdf, with the table rules-table.tex: the table of the rules and the unused lemmas
DOCUMENT = r"""\documentclass[a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage[margin=2cm]{geometry}
\usepackage{booktabs}
\usepackage{longtable}
\usepackage{graphicx}
\pagestyle{empty}
\begin{document}
\begin{center}
{\Large\bfseries Rewrite rules used by Cuvée\par}
\medskip
{\small <subtitle>\par}
{\small\today\par}
\end{center}

The rules applied in the tasks that Cuvée proves (option \texttt{-rules}), by their names: the lemmas of
\texttt{teq.dfy} and of the inputs, and the definitions of functions; per benchmark the number of proved tasks
that use the rule and its applications in them, upper bounds, since rewrites in subterms that are dropped later
count as well. <proved>

\begin{center}
\includegraphics[width=\textwidth]{rules-frequency.pdf}
\end{center}

{\footnotesize
\input{rules-table.tex}
}

\section*{Unused lemmas of \texttt{teq.dfy}}
<unused> of the <lemmas> lemmas of \texttt{teq.dfy} and its modules are used by no proved task:
{\footnotesize\raggedright <list>\par}
\end{document}
"""

# since 0.41.2: the rules applied by each -prove (formerly -simplify) to an assertion, (set-info :used ((name count) ...)), in SMT-LIB
# on stderr with a solver or -verify, as info :used := ((name count) ...) in Dafny output
INFO = re.compile(r":used\s*(?::=)?\s*\(((?:\s*\(\s*[^\s()]+\s+\d+\s*\))*)\s*\)")
PAIR = re.compile(r"\(\s*([^\s()]+)\s+(\d+)\s*\)")
# before 0.41.2: "used by goal 1, which simplified to true: counter_def 1, stores 1" (or "none") on stderr
CLOSED = re.compile(r"^used by .+?, which simplified to true: (.*)$", re.M)
# before 0.41.2: :used (name count) of the goals that remain, also across lines and as {:used (name count)} in Dafny
USED = re.compile(r":used \(\s*([^\s()]+)\s+(\d+)\s*\)")


def logs(results: common.Results) -> dict[str, str]:
    """The logs of the runs of `results` by the file names of their tasks, e.g. simple_3-1.yml, from the files of
    all its parts (common.PARTS), the most recent winning, as in the merged runs."""
    found = {}
    for file in reversed(results.paths or (results.path,)):
        stem = file.name.split(".results.", 1)[0]
        archive = file.with_name(stem + ".logfiles.zip")
        folder = file.with_name(stem + ".logfiles")
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
    text = " ".join(log.split())
    for pairs in INFO.findall(text):
        for name, n in PAIR.findall(pairs):
            used[name] += int(n)
    for name, n in USED.findall(text):
        used[name] += int(n)
    return used


def lemmas(paths: list[Path] = DATABASE) -> list[str]:
    """The names of the lemmas of teq.dfy and its migrated modules, in their order."""
    text = "".join(path.read_text() for path in paths if path.is_file())
    return re.findall(r"^lemma\s+(?:\{:[^}]*\}\s*)*(\w+)", text, re.M)


def frequency(collected, totals, ranked, labels, path):
    """A bar chart of the rules in the order of the table, by the number of proved tasks that use them, without the
    names of the rules, which are too many for the axis; the axis of the tasks is logarithmic, such that the rules
    that few tasks use stay visible; the bars of several benchmarks stand next to each other."""
    plt = common.pyplot()
    colors = common.colors(list(collected))
    figure, axes = plt.subplots(figsize=(7, 3))
    width = 0.8 / len(collected)
    for i, tool in enumerate(collected):
        xs = [rank + i * width for rank in range(len(ranked))]
        ys = [totals[tool].get(rule, (0, 0))[0] for rule, _ in ranked]
        axes.bar(xs, ys, width=width, color=colors[tool], label=labels[tool], align="edge")
    axes.set_yscale("log")
    axes.set_xlim(0, len(ranked))
    axes.set_xticks([])
    axes.set_xlabel(f"rules, by the number of tasks that use them ({len(ranked)} rules)")
    axes.set_ylabel("proved tasks")
    axes.grid(axis="y", which="both", linewidth=0.3, alpha=0.5)
    if len(collected) > 1:
        # below the axes and their label, such that it covers no bar
        axes.legend(loc="upper center", bbox_to_anchor=(0.5, -0.16), ncol=2, frameon=False)
    figure.tight_layout()
    figure.savefig(path, bbox_inches="tight")
    plt.close(figure)


def main():
    parser = common.arguments(__doc__.splitlines()[0])
    parser.set_defaults(tools=["cuvee", "cuvee-fallback"])
    parser.add_argument("--top", type=int, default=0, help="the number of rules in the LaTeX table (default: 0, all)")
    parser.add_argument("--no-pdf", action="store_true", help="write the CSV and LaTeX files only")
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
    labels = common.labels(collected)
    columns = len(collected)
    # the benchmarks over their two columns, underlined, then the names of the columns; repeated on further pages
    head = [" & " + " & ".join(rf"\multicolumn{{2}}{{c}}{{{labels[tool]}}}" for tool in collected) + r" \\"]
    head += ["".join(rf"\cmidrule(lr){{{2 + 2 * i}-{3 + 2 * i}}}" for i in range(columns))]
    head += ["rule & " + " & ".join(["tasks & applications"] * columns) + r" \\", r"\midrule"]
    lines = [r"\begin{longtable}{@{}l" + "rr" * columns + "@{}}", r"\toprule"] + head + [r"\endfirsthead"]
    lines += [rf"\multicolumn{{{1 + 2 * columns}}}{{@{{}}l}}{{\emph{{continued}}}} \\", r"\toprule"] + head + [r"\endhead"]
    lines += [r"\bottomrule", r"\endlastfoot"]
    totals = {tool: {row[2]: (row[3], row[4]) for row in rows if row[0] == tool and row[1] == "Total"} for tool in collected}
    ranking = collections.Counter()
    for tool in collected:
        for rule, (n, _) in totals[tool].items():
            ranking[rule] = max(ranking[rule], n)
    ranked = sorted(ranking.items(), key=lambda item: (-item[1], item[0]))
    frequency(collected, totals, ranked, labels, args.output / "rules-frequency.pdf")
    for rule, _ in ranked[: args.top] if args.top > 0 else ranked:
        cells = []
        for tool in collected:
            n, m = totals[tool].get(rule, (0, 0))
            cells += [str(n), str(m)]
        lines.append(r"\texttt{" + rule.replace("_", r"\_") + "} & " + " & ".join(cells) + r" \\")
    lines += [r"\end{longtable}", ""]
    (args.output / "rules-table.tex").write_text("\n".join(lines))

    # the lemmas of teq.dfy that no proved task of any benchmark uses
    used = set(ranking)
    unused = [name for name in lemmas() if name not in used]
    (args.output / "rules-unused.txt").write_text("".join(name + "\n" for name in unused))

    for tool in collected:
        print(f"{labels[tool]}: {sum(proved[k] for k in proved if k[0] == tool)} proved tasks, {len(totals[tool])} rules used")
    print(f"{len(unused)} of {len(lemmas())} lemmas of teq.dfy and its modules unused")
    print(args.output / "rules.csv")
    print(args.output / "rules-table.tex")
    print(args.output / "rules-frequency.pdf")

    if not args.no_pdf:
        categories = sorted({key[1] for key in tasks})
        counts_per = "; ".join(
            f"{labels[tool]}: " + ", ".join(f"{proved[(tool, name)]} in {name}" for name in categories if (tool, name) in proved)
            for tool in collected
        )
        document = (
            DOCUMENT.replace("<subtitle>", "categories " + ", ".join(categories))
            .replace("<proved>", "Proved tasks: " + counts_per + ".")
            .replace("<unused>", str(len(unused)))
            .replace("<lemmas>", str(len(lemmas())))
            .replace("<list>", ", ".join(r"\texttt{" + name.replace("_", r"\_") + "}" for name in unused))
        )
        (args.output / "rules.tex").write_text(document)
        print(pdflatex(args.output, "rules", runs=2))


if __name__ == "__main__":
    main()
