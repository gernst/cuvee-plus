"""Shared code of the scripts that format the experimental results.

BenchExec writes one result file per benchmark (e.g. cuvee-15min, symbiotic) and task set (its block,
e.g. C.unreach-call.Loops or Loops). The scripts take the most recent file for each pair, so that a
rerun of one tool or of one category replaces the older results without further configuration. A category
may be run in parts, task sets of their own whose names add a suffix of PARTS (C.unreach-call.Loops-split, the
tasks of Loops that xml/cuvee-acsl.xml runs with -split): the most recent file of each part is merged into the
category, task by task, the most recent file winning.
"""

import argparse
import bz2
import re
import sys
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
RESULTS = SCRIPTS.parent / "results"
OUTPUT = SCRIPTS / "out"
# results of SV-COMP 2026 from https://sv-comp.sosy-lab.org/2026/results/results-verified/ (the .fixed files,
# whose categories include the validation of the witnesses)
OFFICIAL = SCRIPTS / "official"

# the benchmarks compared by default, in the order of the columns and legends: Cuvée with the full lemma database
# (cuvee-full.xml, cuvee-full-fallback.xml, 15 min) and with Horn clauses for z3 (cuvee-chc.xml), the other runs
# of Cuvée are left out
TOOLS = ["cuvee-full", "cuvee-full-fallback", "cuvee-chc", "symbiotic", "aise", "uautomizer", "cpachecker", "korn"]

CATEGORIES = ["Arrays", "Loops"]

# names for display; other benchmarks fall back to the displayName of their definition, e.g. cuvee (Cuvée,
# whose time limit was 1 min in the runs on Arrays and Loops); cuvee-full, with all modules of the lemma
# database, is Cuvée (TEQ), as the configuration of the comparison; Cuvée+Z3 (TEQ) is Cuvée (TEQ) with -fallback,
# which hands the goals to z3
LABELS = {
    "cuvee-15min": "Cuvée (TEQ)",
    "cuvee-fallback": "Cuvée+Z3 (TEQ)",
    "cuvee-full": "Cuvée (TEQ)",
    "cuvee-full-fallback": "Cuvée+Z3 (TEQ)",
    "cuvee-chc": "Cuvée (CHC)",
    "symbiotic": "Symbiotic",
    "aise": "AISE",
    "uautomizer": "UAutomizer",
    "cpachecker": "CPAchecker",
    "korn": "Korn",
    "pysvlib-chc": "PySvLib-CHC",
    "svlibchecker": "SvLibChecker",
}

# scores of SV-COMP for verdicts on reachability: a wrong proof costs twice as much as a wrong alarm
SCORES = {
    ("correct", "true"): 2,
    ("correct", "false"): 1,
    ("wrong", "true"): -32,
    ("wrong", "false"): -16,
}

# the suffixes of the task sets that are parts of a category, e.g. Loops-split of Loops
PARTS = ("-split",)

FILENAME = re.compile(r"^(?P<benchmark>.+)\.(?P<date>\d{4}-\d\d-\d\d_\d\d-\d\d-\d\d)\.results\..+\.xml\.bz2$")


@dataclass(frozen=True)
class Run:
    task: str  # e.g. loops/array-1.yml, below sv-benchmarks/c
    category: str  # e.g. Loops
    status: str  # as reported by the tool-info module, e.g. true, false(unreach-call), TIMEOUT
    result: str  # as classified by BenchExec: correct, wrong, unknown, error, ...
    cputime: float | None

    @property
    def verdict(self) -> str | None:
        if self.status == "true":
            return "true"
        if self.status.startswith("false"):
            return "false"
        return None

    @property
    def outcome(self) -> tuple[str, str] | None:
        """(correct|wrong, true|false), or None for runs without a verdict."""
        if self.result in ("correct", "wrong") and self.verdict:
            return (self.result, self.verdict)
        return None

    @property
    def unconfirmed(self) -> bool:
        """A correct verdict whose witness was not validated, which SV-COMP scores with 0."""
        return self.result == "correct-unconfirmed"

    @property
    def solved(self) -> bool:
        return self.result == "correct" and self.cputime is not None

    @property
    def score(self) -> int:
        return SCORES.get(self.outcome, 0)


@dataclass(frozen=True)
class Results:
    benchmark: str
    label: str
    category: str
    date: str
    version: str
    timelimit: float  # seconds of CPU time
    memlimit: str
    cores: str
    cpus: list[str]  # the models of the CPUs of the hosts that ran the tasks, e.g. Intel Core i9-9900 @ 3.10 GHz
    path: Path  # the most recent of the merged files
    runs: list[Run]
    paths: tuple[Path, ...] = ()  # all merged files, one per part of the category (see PARTS)


def label(benchmark: str, attributes: dict[str, str] | None = None) -> str:
    if benchmark in LABELS:
        return LABELS[benchmark]
    if attributes and attributes.get("displayName"):
        return attributes["displayName"]
    return benchmark


def header(path: Path) -> dict[str, str]:
    """The attributes of the root element, without parsing the runs."""
    with bz2.open(path) as file:
        for _, element in ET.iterparse(file, events=("start",)):
            return dict(element.attrib)
    return {}


def category(block: str) -> str:
    # C.unreach-call.Loops and Loops (older definitions of Cuvée) are the same category; tasks in other
    # languages keep theirs, e.g. Boogie.unreach-call.RAPID is RAPID (Boogie)
    parts = block.split(".")
    name = parts[-1]
    for suffix in PARTS:
        name = name.removesuffix(suffix)
    if len(parts) == 3 and parts[0] != "C":
        return f"{name} ({parts[0]})"
    return name


def newest(found: list[tuple[str, str, Path]]) -> list[Path]:
    """The most recent file of each block among (date, block, path), the most recent overall first."""
    per_block: dict[str, tuple[str, Path]] = {}
    for date, block, path in found:
        if block not in per_block or per_block[block][0] < date:
            per_block[block] = (date, path)
    return [path for _, path in sorted(per_block.values(), reverse=True)]


def latest(results: Path = RESULTS) -> dict[tuple[str, str], list[Path]]:
    """The most recent result file for each benchmark, category, and part of it (see PARTS), the most recent
    first."""
    found: dict[tuple[str, str], list[tuple[str, str, Path]]] = {}
    for path in results.glob("*.results.*.xml.bz2"):
        match = FILENAME.match(path.name)
        if not match:
            continue
        # files without a block combine all task sets of a run definition and duplicate the others
        block = header(path).get("block")
        if not block:
            continue
        found.setdefault((match["benchmark"], category(block)), []).append((match["date"], block, path))
    return {key: newest(files) for key, files in found.items()}


def seconds(value: str | None) -> float | None:
    if value is None:
        return None
    return float(value.rstrip("s"))


def task(name: str) -> str:
    # tasks of sv-benchmarks by their path in the repository, others (e.g. Dafny) without leading ../
    marker = "sv-benchmarks/c/"
    if marker in name:
        return name.split(marker, 1)[1]
    while name.startswith("../"):
        name = name[3:]
    return name


def load(benchmark: str, path: Path | list[Path]) -> Results:
    """The results of a file, or of the files of the parts of a category, the most recent first (see latest),
    merged task by task, the most recent file with a status winning (a run stopped before the task finished has
    none); the attributes are those of the most recent file."""
    paths = [path] if isinstance(path, Path) else path
    merged: dict[str, Run] = {}
    for part in reversed(paths):
        for run in runs(part):
            if run.status or run.task not in merged:
                merged[run.task] = run
    root = ET.parse(bz2.open(paths[0])).getroot()
    path = paths[0]
    name = category(root.get("block", ""))
    return Results(
        benchmark=benchmark,
        label=label(benchmark, root.attrib),
        category=name,
        date=root.get("date", ""),
        version=root.get("version", ""),
        timelimit=seconds(root.get("timelimit")) or 0.0,
        memlimit=root.get("memlimit", ""),
        cores=root.get("cpuCores", ""),
        cpus=sorted({cpu.get("model", "") for cpu in root.iter("cpu")} - {""}),
        path=path,
        runs=list(merged.values()),
        paths=tuple(paths),
    )


def runs(path: Path) -> list[Run]:
    root = ET.parse(bz2.open(path)).getroot()
    name = category(root.get("block", ""))
    found = []
    for run in root.iter("run"):
        columns = {column.get("title"): column.get("value") for column in run.iter("column")}
        found.append(
            Run(
                task=task(run.get("name", "")),
                category=name,
                status=columns.get("status") or "",
                result=columns.get("category") or "",
                cputime=seconds(columns.get("cputime")),
            )
        )
    return found


def collect(tools: list[str], categories: list[str], results: Path = RESULTS, quiet: bool = False) -> dict[str, dict[str, Results]]:
    """The results of each tool per category; tools or categories without results are skipped, and reported
    unless quiet, e.g. for the results of SV-COMP, which lack Cuvée and the categories a tool did not enter."""
    files = latest(results)
    collected: dict[str, dict[str, Results]] = {}
    for tool in tools:
        for name in categories:
            paths = files.get((tool, name))
            if paths is None:
                if not quiet:
                    print(f"no results for {tool} on {name} in {results}", file=sys.stderr)
                continue
            collected.setdefault(tool, {})[name] = load(tool, paths)
    return collected


def arguments(description: str) -> argparse.ArgumentParser:
    """The options shared by all scripts; each script adds its own."""
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("--results", type=Path, default=RESULTS, help=f"directory of BenchExec results (default: {RESULTS})")
    parser.add_argument("--tools", type=lambda value: value.split(","), default=TOOLS, help=f"comma-separated benchmark names (default: {','.join(TOOLS)})")
    parser.add_argument("--categories", type=lambda value: value.split(","), default=CATEGORIES, help=f"comma-separated categories (default: {','.join(CATEGORIES)})")
    parser.add_argument("--official", type=Path, default=OFFICIAL, help=f"directory of the results of SV-COMP (default: {OFFICIAL})")
    parser.add_argument("--output", type=Path, default=OUTPUT, help=f"directory for the generated files (default: {OUTPUT})")
    return parser


def available(collected: dict[str, dict[str, Results]], tools: list[str]) -> list[str]:
    """The tools with results, in the requested order."""
    return [tool for tool in tools if tool in collected]


def labels(collected: dict[str, dict[str, Results]]) -> dict[str, str]:
    return {tool: next(iter(results.values())).label for tool, results in collected.items()}


def pyplot():
    """matplotlib for writing PDF files, with fonts embedded as TrueType so that the PDFs can be edited."""
    import matplotlib

    matplotlib.use("pdf")
    import matplotlib.pyplot as plt

    plt.rcParams.update(
        {
            "pdf.fonttype": 42,
            "font.size": 9,
            "axes.titlesize": 10,
            "legend.fontsize": 8,
            "figure.dpi": 150,
        }
    )
    return plt


# a fixed color and marker per tool, the same in all plots: the configurations of Cuvée in blues and greens, their
# portfolios in purples, the other verifiers in warm colors and greys; the names of older runs share the style of
# the configuration they stand for
STYLES = {
    "cuvee": ("#1f77b4", "o"),
    "cuvee-full": ("#1f77b4", "o"),
    "cuvee-15min": ("#1f77b4", "o"),
    "cuvee-fallback": ("#17becf", "s"),
    "cuvee-full-fallback": ("#17becf", "s"),
    "cuvee-chc": ("#2ca02c", "^"),
    "cuvee-acsl": ("#bcbd22", "P"),
    "TEQ + CHC": ("#9467bd", "v"),
    "TEQ+Z3 + CHC": ("#e377c2", "D"),
    "symbiotic": ("#d62728", "X"),
    "aise": ("#ff7f0e", "<"),
    "uautomizer": ("#8c564b", ">"),
    "cpachecker": ("#7f7f7f", "*"),
    "korn": ("#000000", "h"),
    "monocera": ("#ff9896", "p"),
    "tricera": ("#c49c94", "H"),
    "pysvlib-chc": ("#e7ba52", "d"),
    "svlibchecker": ("#843c39", "8"),
}


def colors(tools: list[str]) -> dict[str, str]:
    """One color per tool, the same in all plots (STYLES); tools without a style get the colors of a palette in
    the order of their names."""
    palette = ["#aec7e8", "#ffbb78", "#98df8a", "#c5b0d5", "#c49c94", "#f7b6d2", "#dbdb8d", "#9edae5"]
    others = sorted(tool for tool in tools if tool not in STYLES)
    return {tool: STYLES[tool][0] if tool in STYLES else palette[others.index(tool) % len(palette)] for tool in tools}


def markers(tools: list[str]) -> dict[str, str]:
    """One marker per tool, the same in all plots (STYLES)."""
    fallback = ["o", "s", "^", "v", "D", "P", "X", "*"]
    others = sorted(tool for tool in tools if tool not in STYLES)
    return {tool: STYLES[tool][1] if tool in STYLES else fallback[others.index(tool) % len(fallback)] for tool in tools}