#!/usr/bin/env python3
"""Scatter plots comparing the CPU times of two tools task by task.

Without tools as arguments, every pair of the selected tools gets a plot. Each point is a task that at
least one of the two solves correctly; tasks that only one solves lie on the line "unsolved" of the
other. Points below the diagonal are faster for the tool on the y axis.
"""

import itertools
import sys

import common


def solved(results: dict[str, common.Results], categories: list[str]) -> dict[tuple[str, str], float | None]:
    """The CPU time per task (category, name), None for tasks without a correct result."""
    return {
        (run.category, run.task): run.cputime if run.solved else None
        for name in categories
        if name in results
        for run in results[name].runs
    }


def plot(plt, x: str, y: str, collected, categories: list[str], names: dict[str, str], path):
    first = solved(collected[x], categories)
    second = solved(collected[y], categories)
    # only tasks run by both tools, e.g. Cuvée leaves out VerifyThis-Loops
    tasks = [task for task in first if task in second and (first[task] is not None or second[task] is not None)]
    timelimit = max(each.timelimit for tool in (x, y) for each in collected[tool].values())
    known = [time for task in tasks for time in (first[task], second[task]) if time is not None]
    if not known:
        return False
    lower = max(min(known) / 2, 0.01)
    unsolved = timelimit * 2.5

    figure, axes = plt.subplots(figsize=(4.4, 4.4))
    markers = ["o", "s", "^", "D"]
    for index, name in enumerate(categories):
        points = [task for task in tasks if task[0] == name]
        if not points:
            continue
        axes.scatter(
            [first[task] if first[task] is not None else unsolved for task in points],
            [second[task] if second[task] is not None else unsolved for task in points],
            s=10,
            alpha=0.6,
            marker=markers[index % len(markers)],
            linewidths=0,
            label=f"{name} ({len(points)})",
        )

    upper = unsolved * 1.6
    axes.plot([lower, upper], [lower, upper], color="grey", linewidth=0.8)
    for factor in (10, 0.1):
        axes.plot([lower, upper], [lower * factor, upper * factor], color="grey", linewidth=0.5, linestyle=":")
    for line in (axes.axvline, axes.axhline):
        line(timelimit, color="grey", linestyle="--", linewidth=0.6)
    axes.set_xscale("log")
    axes.set_yscale("log")
    axes.set_xlim(lower, upper)
    axes.set_ylim(lower, upper)
    axes.set_aspect("equal")

    # the decades below the time limit as ticks, the band beyond it as unsolved
    ticks = [10.0**exponent for exponent in range(-2, 5) if lower <= 10.0**exponent < timelimit]
    for setter in (axes.set_xticks, axes.set_yticks):
        setter(ticks + [unsolved], [f"{tick:g}" for tick in ticks] + ["unsolved"])
    axes.minorticks_off()

    only_x = sum(first[task] is not None and second[task] is None for task in tasks)
    only_y = sum(first[task] is None and second[task] is not None for task in tasks)
    both = sum(first[task] is not None and second[task] is not None for task in tasks)
    axes.set_title(f"both {both}, only {names[x]} {only_x}, only {names[y]} {only_y}", fontsize=8)
    axes.set_xlabel(f"CPU time of {names[x]} (s)")
    axes.set_ylabel(f"CPU time of {names[y]} (s)")
    axes.grid(True, which="major", alpha=0.3)
    # below the axes and their label, such that it covers no curve
    axes.legend(loc="upper center", bbox_to_anchor=(0.5, -0.16), ncol=2, frameon=False)
    figure.savefig(path, bbox_inches="tight")
    plt.close(figure)
    return True


def main():
    parser = common.arguments(__doc__.splitlines()[0])
    parser.add_argument("pair", nargs="*", metavar="tool", help="two benchmark names to compare (default: all pairs of --tools)")
    args = parser.parse_args()
    if args.pair and len(args.pair) != 2:
        parser.error("give two tools or none")

    tools = args.pair or args.tools
    collected = common.collect(tools, args.categories, args.results)
    tools = common.available(collected, tools)
    if len(tools) < 2:
        sys.exit("results of at least two tools are needed")
    names = common.labels(collected)
    plt = common.pyplot()

    args.output.mkdir(parents=True, exist_ok=True)
    for x, y in itertools.combinations(tools, 2):
        path = args.output / f"scatter-{x}-{y}.pdf"
        if plot(plt, x, y, collected, args.categories, names, path):
            print(path)


if __name__ == "__main__":
    main()
