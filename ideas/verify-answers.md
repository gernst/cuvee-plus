# Open points of `-verify`

The answers `correct`/`incorrect`/`unknown` of `-verify` were proposed on Oct 12, 2026 and implemented in 0.41.0
(the sink [pipe/Verify.scala](../src/cuvee/pipe/Verify.scala), see [doc/architecture.md](../doc/architecture.md)):
`-verify` changes only the output, the pipeline is given explicitly, the answers are aggregated over all
obligations so far and given to each `verify-call` or to the end of the input, goals are expected valid and each
`check-sat` satisfiable. The principle: the answer is about the input as specified, so contracts and loop
invariants are specification (a loop invariant too weak for the assertions makes a task `incorrect`), and
`-unbounded` changes the meaning of the task rather than approximating it. What remains open:

1. **Invariants are extended, not checked, by `-chc` and `-teq`.** On a loop whose given invariant is too weak
   (`examples/svlib/vcgen/invalid_invariant.svlib`, `examples/c/verify/vcgen_weak_invariant.c`), `-vcgen` answers
   `incorrect`, `-chc` and `-teq` answer `correct`, since they generate invariants of their own and only check the
   given one at the loop head. Intended with an invariant generator; to be stated as such, or a mode that holds the
   techniques to the given invariants.
2. **Answers to the commands that transforms add.** `Horn` adds `check-sat` and `get-model` at `Done`; after a
   `verify-call` the sink acknowledges `Done` with `success`, which `Pipe.run` does not report, by its rule for
   answers added in front of a command without answer. With `print-success` a `success` appears at the end;
   obligations after the last `verify-call` are checked but not reported.
3. **The work is not done at `verify-call`.** Goals and clauses are emitted when the procedure's definition is
   flushed, which is the `verify-call` in all current tasks but not in general (another query between
   `define-proc` and `verify-call`); each answer covers all procedures so far, not those the call reaches, so an
   earlier, unrelated call can make an answer `incorrect`.
4. **`:abstract` is per procedure.** `VCGen` produces one goal per procedure, so a loop without invariant makes all
   obligations of the procedure `unknown`, also those that do not depend on the loop; `-split` separates them but
   they keep the attribute.
5. **The remaining goals are not visible under `-verify`.** The `:used` rules are reported on stderr since 0.41.2,
   the goals that explain an `unknown` are not; a `-verify -print` that shows them, or a flag, would help the
   benchmark logs.
6. **`cuvee.py` needs `-verify`.** A run without it is an error of the tool-info module; the archive and the
   fm-tools entry pass it, which every new run definition must as well.
7. **Wrong refutations of `-fallback` under `-verify`.** A model of Z3 for a lowered goal is no counterexample,
   since the lowering generalizes (uninterpreted `bitand`, fresh functions for traces); the goals of `-fallback`
   should be `:abstract`, which three tasks of the unbounded set and two of SV-COMP showed were not (see
   [experiments.md](experiments.md), TODO.md).
