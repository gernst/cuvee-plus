#!/usr/bin/env python3
"""Quantile plots of all tools: the n-th fastest correct result against its CPU time.

One plot per category, and one over all categories if there are several. A curve that reaches
further to the right solves more tasks, a lower curve solves them faster.
"""

import sys

import common


def times(results: list[common.Results]) -> list[float]:
    """CPU times of the correct results, fastest first; wrong results count as unsolved."""
    return sorted(run.cputime for each in results for run in each.runs if run.solved)


def plot(plt, title: str, curves: dict[str, list[float]], names: dict[str, str], colors: dict[str, str], timelimit: float, path):
    figure, axes = plt.subplots(figsize=(6, 3.8))
    markers = common.markers(list(curves))
    for tool, values in curves.items():
        if not values:
            continue
        # a few markers per curve tell curves of similar colors apart, without cluttering dense curves
        axes.plot(
            range(1, len(values) + 1),
            values,
            label=f"{names[tool]} ({len(values)})",
            color=colors[tool],
            marker=markers[tool],
            markevery=max(1, len(values) // 8),
            markersize=4,
            linewidth=1.3,
        )
    if timelimit:
        axes.axhline(timelimit, color="grey", linestyle=":", linewidth=0.8)
    axes.set_yscale("log")
    axes.set_xlim(left=0)
    axes.set_xlabel("n-th fastest correct result")
    axes.set_ylabel("CPU time (s)")
    axes.set_title(title)
    axes.grid(True, which="major", alpha=0.3)
    # below the axes and their label, such that it covers no curve
    axes.legend(loc="upper center", bbox_to_anchor=(0.5, -0.16), ncol=2, frameon=False)
    figure.savefig(path, bbox_inches="tight")
    plt.close(figure)


def main():
    parser = common.arguments(__doc__.splitlines()[0])
    args = parser.parse_args()

    collected = common.collect(args.tools, args.categories, args.results)
    tools = common.available(collected, args.tools)
    if not tools:
        sys.exit("no results found")
    names = common.labels(collected)
    colors = common.colors(tools)
    plt = common.pyplot()

    groups = [(name, [name]) for name in args.categories]
    if len(args.categories) > 1:
        groups.append(("all", args.categories))

    args.output.mkdir(parents=True, exist_ok=True)
    for title, included in groups:
        selected = {tool: [collected[tool][name] for name in included if name in collected[tool]] for tool in tools}
        curves = {tool: times(results) for tool, results in selected.items() if results}
        if not curves:
            continue
        timelimit = max((each.timelimit for results in selected.values() for each in results), default=0)
        heading = "All categories" if title == "all" else title
        path = args.output / f"quantile-{title}.pdf"
        plot(plt, heading, curves, names, colors, timelimit, path)
        print(path)


if __name__ == "__main__":
    main()
