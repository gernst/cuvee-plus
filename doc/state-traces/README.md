# Trace equation systems by three examples

`state-traces.tex` explains the approach to a reader who knows verification but not trace equation
systems. It uses three examples of [examples/dafny/state](../../examples/dafny/state) under
`-teq-state -prove`:

- the array initialization and the swap of two arrays: the verification condition over traces, the lemma
  database, and the proofs step by step from the rewrite log;
- the binary search over a sorted array (`bsearch_bisect.dfy`): a loop without a closed form, proved from bounds
  by a lemma about the bisection of an interval as a whole, with sortedness as partition points within the array
  and the bounds as forward facts.

It ends with the engine in short and what the examples do not show. Compile with `pdflatex state-traces.tex`
(twice). Written Oct 13, 2026, with the help of Claude Code (see the AI declaration in the document).
