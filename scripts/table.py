#!/usr/bin/env python3
"""Comparison table of the tools as a LaTeX document, compiled to PDF.

Categories and their totals are the rows, the tools the columns. Tools with results of SV-COMP get a
second column next to ours, which shows how far the limits of our runs (and the validation of the
witnesses in SV-COMP) change the outcome. The table itself is written to table.tex, for inclusion in
other documents, the legend of the tools with their versions to legend.tex, and comparison.tex wraps
both into a document of its own (portrait A4), followed by the scatter plots of scatter.py, if run before.
"""

import itertools
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

import common


@dataclass(frozen=True)
class Column:
    tool: str
    source: str  # "here" for our runs, "SV-COMP" for the official results
    results: dict[str, common.Results]  # per category


def counter(result: str, verdict: str):
    return lambda runs: sum(run.outcome == (result, verdict) for run in runs)


# the rows of each category: name and how to count it from the runs
ROWS = [
    ("tasks", lambda runs: len(runs)),
    ("correct true", counter("correct", "true")),
    ("correct false", counter("correct", "false")),
    ("unconfirmed", lambda runs: sum(run.unconfirmed for run in runs)),
    ("wrong true", counter("wrong", "true")),
    ("wrong false", counter("wrong", "false")),
]

# rows left out where they are 0 for all tools; only the validation of SV-COMP leaves results unconfirmed
OPTIONAL = {"unconfirmed"}

# rows whose largest value is set in bold; not those of wrong results, where most tools share the best value 0
BEST = {"correct true": max, "correct false": max}

# names in LaTeX where they differ from the plain labels of common.LABELS
LATEX = {"cpachecker": r"CPA\checkmark"}

# shorter names in the header of the table, so that it fits on a portrait page; the legend has the full ones
SHORT: dict[str, str] = {}

# the sources of the results in LaTeX, in the header of the table (on two lines) and in the legend
SOURCES = {"here": "here", "SV-COMP": r"\shortstack{SV-COMP\\2026}"}
LEGEND = {"here": "here", "SV-COMP": "SV-COMP 2026"}


def escape(text: str) -> str:
    special = {"&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}", "^": r"\textasciicircum{}"}
    return "".join(special.get(char, char) for char in text)


def latex(tool: str, labels: dict[str, str]) -> str:
    return LATEX.get(tool, escape(labels[tool]))


def short(tool: str, labels: dict[str, str]) -> str:
    return escape(SHORT[tool]) if tool in SHORT else latex(tool, labels)


def number(value: int) -> str:
    # a proper minus sign for negative scores
    return f"$-${-value}" if value < 0 else str(value)


def cells(row: str, values: list[int | None]) -> list[str]:
    """The values of one row, None for columns without results, e.g. a category a tool did not enter."""
    known = [value for value in values if value is not None]
    choose = BEST.get(row)
    best = choose(known) if choose and len(known) > 1 else None
    # no emphasis where all tools agree, e.g. no wrong results at all
    if best is not None and all(value == best for value in known):
        best = None
    return ["--" if value is None else rf"\textbf{{{number(value)}}}" if value == best else number(value) for value in values]


def block(title: str, runs_per_column: list[list[common.Run] | None]) -> list[str]:
    lines = [rf"\multicolumn{{{len(runs_per_column) + 1}}}{{l}}{{\textbf{{{escape(title)}}}}} \\"]
    for row, count in ROWS:
        values = [None if runs is None else count(runs) for runs in runs_per_column]
        if row in OPTIONAL and not any(values):
            continue
        lines.append(r"\quad " + " & ".join([escape(row)] + cells(row, values)) + r" \\")
    return lines


def spans(columns: list[Column]) -> list[tuple[str, int, int]]:
    """Consecutive columns of the same tool: tool, first and last column, counted from 2 after the row names."""
    result: list[tuple[str, int, int]] = []
    for index, column in enumerate(columns, start=2):
        if result and result[-1][0] == column.tool:
            result[-1] = (column.tool, result[-1][1], index)
        else:
            result.append((column.tool, index, index))
    return result


def header(columns: list[Column], labels: dict[str, str]) -> list[str]:
    grouped = spans(columns)
    tools = [rf"\multicolumn{{{last - first + 1}}}{{c}}{{{short(tool, labels)}}}" if last > first else short(tool, labels) for tool, first, last in grouped]
    lines = [" & ".join([""] + tools) + r" \\"]
    # a second line names the source of the results, where a tool has more than one column
    shared = {index for _, first, last in grouped if last > first for index in range(first, last + 1)}
    if shared:
        lines.append("".join(rf"\cmidrule(lr){{{first}-{last}}}" for _, first, last in grouped if last > first))
        sources = [rf"\scriptsize {SOURCES[column.source]}" if index in shared else "" for index, column in enumerate(columns, start=2)]
        lines.append(" & ".join([""] + sources) + r" \\")
    return lines


def table(columns: list[Column], labels: dict[str, str], categories: list[str]) -> str:
    lines = [r"\begin{tabular}{l" + "r" * len(columns) + "}", r"\toprule"] + header(columns, labels) + [r"\midrule"]
    present = [name for name in categories if any(name in column.results for column in columns)]
    for index, name in enumerate(present):
        if index:
            lines.append(r"\midrule")
        lines += block(name, [column.results[name].runs if name in column.results else None for column in columns])
    if len(present) > 1:
        # no total for columns that lack a category, which would not compare with the others
        lines.append(r"\midrule")
        lines += block("Total", [[run for name in present for run in column.results[name].runs] if all(name in column.results for name in present) else None for column in columns])
    lines += [r"\bottomrule", r"\end{tabular}"]
    return "\n".join(lines) + "\n"


def limits(results: common.Results) -> str:
    memory = results.memlimit.rstrip("B")
    memory = f"{int(memory) / 1e9:g} GB" if memory.isdigit() else results.memlimit
    cores = f"{results.cores} " + ("core" if results.cores == "1" else "cores")
    return f"{results.timelimit:g} s, {memory}, {cores}"


def cpu(results: common.Results) -> str:
    # the vendor is part of every model name and adds nothing
    return ", ".join(model.removeprefix("Intel ") for model in results.cpus)


def legend(columns: list[Column], labels: dict[str, str]) -> str:
    """The tools with the versions and limits of their runs, per category where these differ."""
    lines = [r"\begin{tabular}{llllll}", r"\toprule", r"tool & & results & version & limits & CPU \\", r"\midrule"]
    previous = None
    for column in columns:
        runs = list(column.results.values())
        if len({(results.version, limits(results), cpu(results)) for results in runs}) == 1:
            rows = [(runs[0].version, limits(runs[0]), cpu(runs[0]))]
        else:
            rows = [(f"{results.version} ({results.category})", limits(results), cpu(results)) for results in runs]
        for index, (version, bound, model) in enumerate(rows):
            first = column.tool != previous
            tool = latex(column.tool, labels) if first else ""
            # the abbreviation used in the header of the table, where there is one
            abbreviation = f"({escape(SHORT[column.tool])})" if first and column.tool in SHORT else ""
            source = escape(LEGEND[column.source]) if index == 0 else ""
            lines.append(" & ".join([tool, abbreviation, source, escape(version), escape(bound), escape(model)]) + r" \\")
            previous = column.tool
    lines += [r"\bottomrule", r"\end{tabular}"]
    return "\n".join(lines) + "\n"


DOCUMENT = r"""\documentclass[a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage[margin=2cm]{geometry}
\usepackage{booktabs}
\usepackage{amssymb}
\usepackage{graphicx}
\pagestyle{empty}
\setlength{\tabcolsep}{3pt}
% scales a table down to the width of the page, but never up; \leavevmode puts it into a centered line
\newcommand{\fit}[1]{\setbox0\hbox{#1}\leavevmode\ifdim\wd0>\textwidth\resizebox{\textwidth}{!}{\box0}\else\box0\fi}
\input{facts.tex}
\begin{document}
\begin{center}
{\Large\bfseries <title>\par}
\medskip
{\small\today\par}
\end{center}

\input{setup.tex}

\section*{Results}
\begin{center}
\footnotesize
\fit{\input{table.tex}}

\bigskip
Unconfirmed: correct, but the witness was not validated in SV-COMP.
Our runs do not validate witnesses, so no scores are given.

\bigskip
\input{legend.tex}
\end{center}
<scatter>\end{document}
"""

# the title of the document
TITLE = r"Cuvée and the verifiers of SV-COMP 2026\\[0.5ex] on ReachSafety-Arrays and ReachSafety-Loops"


def facts(columns: list[Column]) -> str:
    """Macros for setup.tex: the numbers of tasks and the limits of most of our runs."""
    ours = [results for column in columns if column.source == "here" for results in column.results.values()]
    tasks = {}
    for results in ours:
        tasks[results.category] = max(tasks.get(results.category, 0), len(results.runs))
    common_limits = max({(r.timelimit, r.memlimit, r.cores) for r in ours}, key=lambda key: sum((r.timelimit, r.memlimit, r.cores) == key for r in ours))
    timelimit, memlimit, cores = common_limits
    memory = f"{int(memlimit.rstrip('B')) / 1e9:g}\\,GB" if memlimit.rstrip("B").isdigit() else escape(memlimit)
    lines = [rf"\newcommand{{\{name.replace(' ', '').replace('(', '').replace(')', '')}Tasks}}{{{count}}}" for name, count in sorted(tasks.items())]
    lines += [rf"\newcommand{{\TimeLimit}}{{{timelimit:g}\,s}}", rf"\newcommand{{\MemoryLimit}}{{{memory}}}", rf"\newcommand{{\Cores}}{{{cores}}}"]
    return "\n".join(lines) + "\n"


def scatter(output: Path, tools: list[str]) -> str:
    """The scatter plots of scatter.py found in the output directory, two per row, in the order of the tools."""
    plots = [f"scatter-{x}-{y}.pdf" for x, y in itertools.combinations(tools, 2) if (output / f"scatter-{x}-{y}.pdf").exists()]
    if not plots:
        return ""
    lines = [r"\clearpage", r"\section*{Scatter plots}", r"\noindent"]
    for index, plot in enumerate(plots):
        lines.append(rf"\includegraphics[width=0.49\textwidth]{{{plot}}}" + (r"\\[1ex]" if index % 2 else r"\hfill"))
    return "\n".join(lines) + "\n"


def pdflatex(output: Path, name: str, runs: int = 1) -> Path:
    """`name`.pdf in `output`, compiled `runs` times, e.g. twice for the column widths of a longtable."""
    command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", f"{name}.tex"]
    for _ in range(runs):
        process = subprocess.run(command, cwd=output, stdin=subprocess.DEVNULL, capture_output=True, text=True)
        if process.returncode != 0:
            print(process.stdout[-3000:], file=sys.stderr)
            sys.exit(f"pdflatex failed, see {output / (name + '.log')}")
    for suffix in (".aux", ".log"):
        (output / f"{name}{suffix}").unlink(missing_ok=True)
    return output / f"{name}.pdf"


def main():
    parser = common.arguments(__doc__.splitlines()[0])
    parser.add_argument("--no-official", action="store_true", help="leave out the results of SV-COMP")
    parser.add_argument("--no-pdf", action="store_true", help="write the LaTeX files only")
    args = parser.parse_args()

    ours = common.collect(args.tools, args.categories, args.results)
    official = {} if args.no_official or not args.official.is_dir() else common.collect(args.tools, args.categories, args.official, quiet=True)
    columns = []
    for tool in args.tools:
        if tool in ours:
            columns.append(Column(tool, "here", ours[tool]))
        if tool in official:
            columns.append(Column(tool, "SV-COMP", official[tool]))
    if not columns:
        sys.exit("no results found")
    labels = {**common.labels(official), **common.labels(ours)}

    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "table.tex").write_text(table(columns, labels, args.categories))
    (args.output / "legend.tex").write_text(legend(columns, labels))
    # tools in the order of the columns, which scatter.py follows in the names of its plots
    tools = list(dict.fromkeys(column.tool for column in columns))
    (args.output / "facts.tex").write_text(facts(columns))
    shutil.copyfile(common.SCRIPTS / "setup.tex", args.output / "setup.tex")
    document = DOCUMENT.replace("<title>", TITLE).replace("<scatter>", scatter(args.output, tools))
    (args.output / "comparison.tex").write_text(document)
    if args.no_pdf:
        print(args.output / "comparison.tex")
    else:
        print(pdflatex(args.output, "comparison"))


if __name__ == "__main__":
    main()
