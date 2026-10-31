#!/usr/bin/env python3
"""The experiments of doc/benchmarks.md ("Experiments of the paper") as one LaTeX document, compiled to PDF.

Each experiment takes, for each benchmark and category, the most recent result file that meets its requirements
(options such as -verify or -unbounded, and the time limit), so that older runs of other configurations are not
mixed in; missing results are blanks (--) until the runs are done. The other verifiers on SV-COMP come from the
official results of SV-COMP 2026 (scripts/official), MonoCera's paper from its Table 3. Tables and plots are
written to the output directory, experiments.tex includes them.
"""

import bz2
import sys
import xml.etree.ElementTree as ET
from dataclasses import dataclass, replace
from pathlib import Path

import common
import quantile
import table

# the time limit of the experiments, in seconds of CPU time, and the exception of the ACSL tasks, run with 60 s
FULL = 900.0


@dataclass(frozen=True)
class Need:
    """What a result file must have: options of the tool (of the run definition or of the task set) and the time
    limit, None for any."""

    options: tuple[str, ...] = ()
    timelimit: float | None = FULL
    # prefixes of the version of the tool, e.g. "0.42." for the runs before the migration of the lemma database
    version: str | tuple[str, ...] | None = None


def options(path: Path) -> set[str]:
    """The options of the root and of the first run, which carries those of its task set, e.g. -unbounded."""
    found: set[str] = set()
    with bz2.open(path) as file:
        for _, element in ET.iterparse(file, events=("start",)):
            if element.tag == "result":
                found |= set(element.get("options", "").split())
            elif element.tag == "run":
                found |= set(element.get("options", "").split())
                break
    return found


def find(benchmark: str, name: str, need: Need, directory: Path = common.RESULTS) -> common.Results | None:
    """The most recent results of `benchmark` on category `name` that meet `need`, merged with the most recent
    results of the other parts of the category that meet it (common.PARTS)."""
    candidates = []
    for path in directory.glob(f"{benchmark}.*.results.*.xml.bz2"):
        match = common.FILENAME.match(path.name)
        if not match or match["benchmark"] != benchmark:
            continue
        attributes = common.header(path)
        if common.category(attributes.get("block", "")) != name:
            continue
        if need.timelimit is not None and common.seconds(attributes.get("timelimit")) != need.timelimit:
            continue
        if need.version is not None and not attributes.get("version", "").startswith(need.version):
            continue
        if not set(need.options) <= options(path):
            continue
        candidates.append((match["date"], attributes.get("block", ""), path))
    if not candidates:
        return None
    return common.load(benchmark, common.newest(candidates))


def gather(benchmark: str, categories: list[str], need: Need, directory: Path = common.RESULTS) -> dict[str, common.Results]:
    found = {name: find(benchmark, name, need, directory) for name in categories}
    return {name: results for name, results in found.items() if results is not None}


# the labels of the columns, also for tools without results yet, named as in the paper (TEQ, TEQ+Z3, CHC)
LABELS = {
    **common.LABELS,
    "cuvee": "TEQ",
    "cuvee-fallback": "TEQ+Z3",
    "cuvee-chc": "CHC",
    "monocera": "MonoCera",
    "tricera": "TriCera",
    "cuvee-acsl": "VC (ACSL)",
}


def grid(spec: list[table.Column], categories: list[str]) -> str:
    """The table of table.py, but with every category, also those without any results yet (dashes), and the total
    only for columns with all categories."""
    lines = [r"\begin{tabular}{l" + "r" * len(spec) + "}", r"\toprule"] + table.header(spec, LABELS) + [r"\midrule"]
    for index, name in enumerate(categories):
        if index:
            lines.append(r"\midrule")
        lines += table.block(name, [column.results[name].runs if name in column.results else None for column in spec])
    if len(categories) > 1:
        lines.append(r"\midrule")
        lines += table.block("Total", [[run for name in categories for run in column.results[name].runs] if all(name in column.results for name in categories) else None for column in spec])
    lines += [r"\bottomrule", r"\end{tabular}"]
    return "\n".join(lines) + "\n"


def transposed(spec: list[table.Column], categories: list[str]) -> str:
    """The table with a row per configuration and, per category and in total, the columns correct true, correct
    false, and wrong (true and false); the best value of a column in bold, a dash where results are missing."""
    groups = categories + (["Total"] if len(categories) > 1 else [])
    measures = [
        ("true", lambda runs: sum(run.outcome == ("correct", "true") for run in runs), max),
        ("false", lambda runs: sum(run.outcome == ("correct", "false") for run in runs), max),
        ("wrong", lambda runs: sum(run.outcome is not None and run.outcome[0] == "wrong" for run in runs), None),
    ]

    def runs(column: table.Column, group: str) -> list[common.Run] | None:
        names = categories if group == "Total" else [group]
        if not all(name in column.results for name in names):
            return None
        return [run for name in names for run in column.results[name].runs]

    values = {column.tool: [[None if runs(column, group) is None else count(runs(column, group)) for _, count, _ in measures] for group in groups] for column in spec}
    lines = [r"\begin{tabular}{l" + ("|rrr" * len(groups)) + "}", r"\toprule"]
    lines.append(" & ".join([""] + [rf"\multicolumn{{3}}{{c}}{{{table.escape(group)}}}" for group in groups]) + r" \\")
    lines.append(" & ".join([""] + [table.escape(name) for _ in groups for name, _, _ in measures]) + r" \\")
    lines.append(r"\midrule")
    for column in spec:
        cells = []
        for g, _ in enumerate(groups):
            for m, (_, _, choose) in enumerate(measures):
                value = values[column.tool][g][m]
                known = [values[other.tool][g][m] for other in spec if values[other.tool][g][m] is not None]
                best = choose(known) if choose and len(known) > 1 and len(set(known)) > 1 else None
                cells.append("--" if value is None else rf"\textbf{{{table.number(value)}}}" if value == best else table.number(value))
        lines.append(" & ".join([table.short(column.tool, LABELS)] + cells) + r" \\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    return "\n".join(lines) + "\n"


def columns(spec: list[tuple[str, str, dict[str, common.Results]]]) -> list[table.Column]:
    return [table.Column(tool, source, results) for tool, source, results in spec]


def pending(spec: list[table.Column], categories: list[str]) -> list[str]:
    """The columns and categories without results, for the note under a table."""
    return [f"{LABELS.get(column.tool, column.tool)} ({', '.join(name for name in categories if name not in column.results)})" for column in spec if any(name not in column.results for name in categories) and column.source == "here"]


def note(missing: list[str]) -> str:
    if not missing:
        return ""
    return r"\par\smallskip{\scriptsize pending: " + table.escape("; ".join(missing)) + r"}"


def legend(spec: list[table.Column]) -> str:
    present = [column for column in spec if column.results]
    if not present:
        return ""
    return table.legend(present, LABELS)


# --- 1. MonoCera ---

MONOCERA = ["MonoCera-Forall", "MonoCera-Max", "MonoCera-Min", "MonoCera-Sum"]

# Table 3 of Amilon et al., CAV 2023 (300 s wall time, AMD Opteron 2220), the SV-COMP tests verified per operator
PAPER = {
    "MonoCera": {"MonoCera-Forall": 27, "MonoCera-Max": 2, "MonoCera-Min": 3, "MonoCera-Sum": 10},
    "TriCera": {"MonoCera-Forall": 0, "MonoCera-Max": 0, "MonoCera-Min": 0, "MonoCera-Sum": 0},
    "CPAchecker": {"MonoCera-Forall": 1, "MonoCera-Max": 0, "MonoCera-Min": 0, "MonoCera-Sum": 0},
    "SeaHorn": {"MonoCera-Forall": 0, "MonoCera-Max": 0, "MonoCera-Min": 0, "MonoCera-Sum": 0},
}


def solved(results: common.Results | None) -> int | None:
    return None if results is None else sum(run.outcome == ("correct", "true") for run in results.runs)


def wrong(results: common.Results | None) -> int | None:
    return None if results is None else sum(run.result == "wrong" for run in results.runs)


def cell(value: int | None) -> str:
    return "--" if value is None else str(value)


def monocera(spec: list[table.Column]) -> str:
    """Tests verified per operator: our runs, then the paper's, which counts verified tests only."""
    head = [LABELS.get(column.tool, column.tool) for column in spec] + [f"{name} (paper)" for name in PAPER]
    lines = [r"\begin{tabular}{lr" + "r" * len(head) + "}", r"\toprule", " & ".join(["operator", "tests"] + [table.escape(name) for name in head]) + r" \\", r"\midrule"]
    totals = [0] * (len(spec) + len(PAPER))
    complete = [True] * len(spec)
    tests = 0
    for name in MONOCERA:
        count = next((len(column.results[name].runs) for column in spec if name in column.results), None)
        tests += count or 0
        values = []
        for index, column in enumerate(spec):
            value = solved(column.results.get(name))
            if value is None:
                complete[index] = False
            else:
                totals[index] += value
            values.append(value)
        for index, numbers in enumerate(PAPER.values(), start=len(spec)):
            totals[index] += numbers[name]
            values.append(numbers[name])
        lines.append(" & ".join([name.removeprefix("MonoCera-").lower(), cell(count)] + table.cells("correct true", values)) + r" \\")
    lines.append(r"\midrule")
    total = [value if index >= len(spec) or complete[index] else None for index, value in enumerate(totals)]
    lines.append(" & ".join(["total", str(tests)] + table.cells("correct true", total)) + r" \\")
    errors = [wrong(None if not column.results else replace(next(iter(column.results.values())), runs=[run for results in column.results.values() for run in results.runs])) for column in spec]
    lines.append(" & ".join(["wrong", ""] + [cell(value) for value in errors] + ["" for _ in PAPER]) + r" \\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    return "\n".join(lines) + "\n"


# --- 3. Complementarity ---


def union(first: common.Results, second: common.Results, benchmark: str) -> common.Results:
    """A virtual portfolio of two runs per task: correct if either is correct, wrong if either is wrong, with the
    smaller CPU time of a correct result."""
    other = {run.task: run for run in second.runs}
    runs = []
    for run in first.runs:
        mate = other.get(run.task)
        candidates = [each for each in (run, mate) if each is not None]
        right = [each for each in candidates if each.result == "correct"]
        bad = [each for each in candidates if each.result == "wrong"]
        if bad:
            runs.append(bad[0])
        elif right:
            runs.append(min(right, key=lambda each: each.cputime or 0.0))
        else:
            runs.append(run)
    return replace(first, benchmark=benchmark, label=benchmark, runs=runs)


# --- 5. ACSL ---


def acsl(annotated: dict[str, common.Results], automatic: dict[str, common.Results], expected: dict[str, bool]) -> str:
    """True tasks proved with the annotations (-vcgen) and by TEQ without them, on the same programs; the tasks of
    benchmarks/acsl keep the folders and names of sv-benchmarks/c."""
    lines = [r"\begin{tabular}{lrrrrr}", r"\toprule", r"category & true tasks & \texttt{-vcgen} (ACSL) & TEQ (no annotations) & both & either \\", r"\midrule"]
    sums = [0] * 5
    complete = True
    for name in common.CATEGORIES:
        if name not in annotated:
            lines.append(rf"{name} & -- & -- & -- & -- & -- \\")
            complete = False
            continue
        true = {run.task for run in annotated[name].runs if expected.get(run.task)}
        proved = {run.task for run in annotated[name].runs if run.outcome == ("correct", "true")}
        if name not in automatic:
            lines.append(rf"{name} & {len(true)} & {len(proved)} & -- & -- & -- \\")
            complete = False
            continue
        auto = {run.task for run in automatic[name].runs if run.outcome == ("correct", "true")} & true
        values = [len(true), len(proved), len(auto), len(proved & auto), len(proved | auto)]
        sums = [a + b for a, b in zip(sums, values)]
        lines.append(" & ".join([name] + [str(value) for value in values]) + r" \\")
    lines.append(r"\midrule")
    lines.append(" & ".join(["total"] + [str(value) if complete else "--" for value in sums]) + r" \\")
    lines += [r"\bottomrule", r"\end{tabular}"]
    return "\n".join(lines) + "\n"


def acsl_task(name: str) -> str:
    return name.split("benchmarks/acsl/")[-1]


def expectations(paths: list[Path]) -> dict[str, bool]:
    """The expected verdicts of the tasks in result files, by the name of the task as in Run.task."""
    expected = {}
    for path in paths:
        for run in ET.parse(bz2.open(path)).getroot().iter("run"):
            verdict = run.get("expectedVerdict")
            if verdict is not None:
                expected[acsl_task(common.task(run.get("name", "")))] = verdict == "true"
    return expected


# --- the document ---

DOCUMENT = r"""\documentclass[a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage[margin=2cm]{geometry}
\usepackage{booktabs}
\usepackage{amssymb}
\usepackage{graphicx}
\pagestyle{plain}
\setlength{\tabcolsep}{3pt}
\newcommand{\fit}[1]{\setbox0\hbox{#1}\leavevmode\ifdim\wd0>\textwidth\resizebox{\textwidth}{!}{\box0}\else\box0\fi}
\newcommand{\plot}[1]{\IfFileExists{#1}{\includegraphics[width=0.49\textwidth]{#1}}{\fbox{\parbox[c][4cm][c]{0.45\textwidth}{\centering\scriptsize #1\\ pending}}}}
\begin{document}
\begin{center}
{\Large\bfseries Experiments: TEQ compared with other techniques\par}
\medskip
{\small\today\par}
\end{center}

\noindent The experiments of \texttt{doc/benchmarks.md}, with the current versions of Cuvée only (0.49 and 0.50,
after the migration of the lemma database and with the answers per goal). Cuvée (TEQ) runs with \texttt{-teq -prove
-split -prove -split -prove} (one trace per strongly connected component of the variables of a loop, the deduction
engine \texttt{-prove}), the lemma database \texttt{teq.dfy} with the modules \texttt{aggregation},
\texttt{arithmetic}, \texttt{arrays}, \texttt{counters}, \texttt{search}, \texttt{sorted}, \texttt{strides},
\texttt{unsigned}; Cuvée+Z3 (TEQ) adds \texttt{-fallback -z3} (one round of \texttt{-split -prove}), Cuvée (CHC) is
\texttt{-simplify -chc -z3}. Cuvée answers each goal, which the tool-info module combines to the verdict, and
writes witnesses (\texttt{-witness}). All our runs: BenchExec, 15\,min CPU time, 7\,GB, 2 cores of an AMD Ryzen 7
PRO 5750G, unless the legends say otherwise. A dash marks results that are missing, listed as pending. No scores
are given, since our runs do not validate witnesses.

\section{Aggregates over arrays: the MonoCera tests}
The 125 SV-COMP tests of Amilon et al.\ (CAV 2023), one per operator (\texttt{\textbackslash forall},
\texttt{\textbackslash max}, \texttt{\textbackslash min}, \texttt{\textbackslash sum}) that the assertion admits,
each tool on the paper's conversion for it, all expected true. As in the paper, with mathematical integers:
Cuvée with \texttt{-unbounded}, MonoCera with TriCera's default \texttt{-arithMode:math}. The columns ``paper''
are Table~3 of the paper (300\,s wall time, AMD Opteron 2220). Tests verified:
\begin{center}\footnotesize
\fit{\input{monocera.tex}}
<monocera-note>
\medskip
<monocera-legend>
\end{center}
\noindent\plot{quantile-monocera.pdf}

\section{SV-COMP ReachSafety-Arrays and -Loops}
Our runs of Cuvée next to the official results of SV-COMP 2026 for the other verifiers, which validate the
witnesses (unconfirmed: correct, but the witness was not validated). Cuvée's witnesses are not validated.
\begin{center}\footnotesize
\fit{\input{svcomp.tex}}
<svcomp-note>
\medskip
<svcomp-legend>
\end{center}
\noindent\plot{quantile-Arrays.pdf}\hfill\plot{quantile-Loops.pdf}

\section{Complementarity of TEQ and Horn clauses}
A virtual portfolio per task: correct if either configuration is correct (the faster one), wrong if either is
wrong.
\begin{center}\footnotesize
\fit{\input{union.tex}}
<union-note>
\end{center}
\noindent\plot{quantile-union.pdf}

\section{Annotations against automation: the ACSL tasks}
The tasks of Arrays and Loops with ACSL (\texttt{benchmarks/acsl}, laid out as in sv-benchmarks, the true tasks
that Cuvée's C supports annotated by a coding agent), checked with \texttt{-vcgen -z3}, \texttt{-split} for the
47 tasks of Loops that need it (a task set of its own, merged into Loops), against TEQ without annotations on the
same programs (Section~2). True tasks proved:
\begin{center}\footnotesize
\fit{\input{acsl.tex}}
\par\medskip
<acsl-legend>
\end{center}

\section{SV-LIB: the verification tasks}
The categories CTranslated (the loop tasks of SV-COMP translated to SV-LIB) and CoreVerification of SV-LIB
(property correct-tags), with the mathematical integers of SMT-LIB; CoreValidation is out of scope. Our runs of
Cuvée next to the official results of all participants of the demonstration category SV-LIB of SV-COMP 2026
(CPAchecker, PySvLib-CHC, SvLibChecker), which validate the witnesses. Each is counted against the expected
verdicts of its own run: those of SV-COMP 2026 (252 and 5 tasks, some without a verdict then), ours of the
current sv-benchmarks (253 and 7 tasks).
\begin{center}\footnotesize
\fit{\input{svlib.tex}}
<svlib-note>
\medskip
<svlib-legend>
\end{center}
\noindent\plot{quantile-svlib.pdf}

\section{Quantified postconditions: the RAPID benchmarks}
The 33 array programs in Boogie of the evaluation of RAPID (Georgiou, Gleiss, Kovács), each one procedure with one
loop without invariant and a quantified postcondition, all expected correct (\texttt{benchmarks/rapid}).
\begin{center}\footnotesize
\fit{\input{rapid.tex}}
<rapid-note>
\medskip
<rapid-legend>
\end{center}
\end{document}
"""


def main():
    parser = common.arguments(__doc__.splitlines()[0])
    parser.add_argument("--no-pdf", action="store_true", help="write the LaTeX files only")
    args = parser.parse_args()
    out = args.output
    out.mkdir(parents=True, exist_ok=True)
    plt = common.pyplot()
    replacements = {}

    # only the runs of the current versions of Cuvée (one trace per component, -prove, the migrated modules, the
    # answers per goal of 0.48.0 without -verify); older runs are not mixed in, their configurations are pending
    # until rerun
    current = ("0.49.", "0.50.")
    teq = Need(version=current)
    unbounded = Need(("-unbounded",), version=current)

    # 1. MonoCera
    spec1 = columns([
        ("cuvee", "here", gather("cuvee", MONOCERA, unbounded)),
        ("cuvee-fallback", "here", gather("cuvee-fallback", MONOCERA, unbounded)),
        ("monocera", "here", gather("monocera", MONOCERA, Need())),
    ])
    (out / "monocera.tex").write_text(monocera(spec1))
    replacements["monocera"] = (note(pending(spec1, MONOCERA)), legend(spec1))
    plots(plt, out, "monocera", spec1, MONOCERA, "MonoCera tests (all operators)")

    # 2. SV-COMP
    categories = common.CATEGORIES
    official = common.collect(["symbiotic", "aise", "uautomizer", "cpachecker", "korn"], categories, args.official, quiet=True)
    spec2 = columns([
        ("cuvee", "here", gather("cuvee", categories, teq)),
        ("cuvee-fallback", "here", gather("cuvee-fallback", categories, teq)),
        ("cuvee-chc", "here", gather("cuvee-chc", categories, Need(version=current))),
    ]) + [table.Column(tool, "SV-COMP", results) for tool, results in official.items()]
    (out / "svcomp.tex").write_text(grid(spec2, categories))
    replacements["svcomp"] = (note(pending(spec2, categories)), legend(spec2))
    for name in categories:
        plots(plt, out, name, spec2, [name], name, file=f"quantile-{name}.pdf")
        # a variant with the legend below the plot, for slides
        plots(plt, out, name, spec2, [name], name, file=f"quantile-{name}-bottom.pdf", legend="bottom")

    # 3. complementarity
    teq_results, z3_results, chc_results = (spec2[0].results, spec2[1].results, spec2[2].results)
    virtual = []
    for label, first in (("TEQ + CHC", teq_results), ("TEQ+Z3 + CHC", z3_results)):
        combined = {name: union(first[name], chc_results[name], label) for name in categories if name in first and name in chc_results}
        LABELS[label] = f"{label} (virtual)"
        virtual.append(table.Column(label, "here", combined))
    spec3 = spec2[:3] + virtual
    (out / "union.tex").write_text(transposed(spec3, categories))
    replacements["union"] = (note(pending(spec3, categories)), "")
    plots(plt, out, "union", spec3, categories, "TEQ and the portfolios (Arrays and Loops)", file="quantile-union.pdf")

    # 4. ACSL, whose tasks are matched with those of sv-benchmarks/c by folder and name
    annotated = gather("cuvee-acsl", categories, Need(version=current))
    expected = expectations([path for results in annotated.values() for path in results.paths])
    annotated = {name: replace(results, runs=[replace(run, task=acsl_task(run.task)) for run in results.runs]) for name, results in annotated.items()}
    (out / "acsl.tex").write_text(acsl(annotated, teq_results, expected))
    replacements["acsl"] = ("", legend(columns([("cuvee-acsl", "here", annotated)])))

    # 5. SV-LIB
    svlib = ["CTranslated (SV-LIB)", "CoreVerification (SV-LIB)"]
    official6 = common.collect(["cpachecker", "pysvlib-chc", "svlibchecker"], svlib, args.official, quiet=True)
    spec6 = columns([
        ("cuvee", "here", gather("cuvee", svlib, teq)),
        ("cuvee-fallback", "here", gather("cuvee-fallback", svlib, teq)),
        ("cuvee-chc", "here", gather("cuvee-chc", svlib, teq)),
    ]) + [table.Column(tool, "SV-COMP", results) for tool, results in official6.items()]
    (out / "svlib.tex").write_text(grid(spec6, svlib))
    replacements["svlib"] = (note(pending(spec6, svlib)), legend(spec6))
    plots(plt, out, "svlib", spec6, svlib, "SV-LIB verification tasks")

    # 6. RAPID
    rapid = ["RAPID (Boogie)"]
    spec7 = columns([
        ("cuvee", "here", gather("cuvee", rapid, teq)),
        ("cuvee-fallback", "here", gather("cuvee-fallback", rapid, teq)),
        ("cuvee-chc", "here", gather("cuvee-chc", rapid, teq)),
    ])
    (out / "rapid.tex").write_text(grid(spec7, rapid))
    replacements["rapid"] = (note(pending(spec7, rapid)), legend(spec7))

    document = DOCUMENT
    for key, (text, legend_text) in replacements.items():
        document = document.replace(f"<{key}-note>", text).replace(f"<{key}-legend>", legend_text)
    (out / "experiments.tex").write_text(document)
    if args.no_pdf:
        print(out / "experiments.tex")
    else:
        print(table.pdflatex(out, "experiments"))


def plots(plt, out: Path, key: str, spec: list[table.Column], categories: list[str], title: str, file: str | None = None,
          legend: str = "right"):
    """A quantile plot of the columns with results; none if there are none, which the document shows as pending."""
    curves = {}
    limit = 0.0
    for column in spec:
        runs = [results for name, results in column.results.items() if name in categories]
        if runs:
            curves[column.tool] = quantile.times(runs)
            limit = max(limit, max(results.timelimit for results in runs))
    path = out / (file or f"quantile-{key}.pdf")
    if not curves:
        path.unlink(missing_ok=True)
        return
    names = {tool: LABELS.get(tool, tool) for tool in curves}
    quantile.plot(plt, title, curves, names, common.colors(list(curves)), limit, path, legend=legend)


if __name__ == "__main__":
    main()
