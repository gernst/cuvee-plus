/-
The part of the semantics of the lemma database of -teq that the printer does not produce: the datatype of traces,
which the generator takes from here (it checks that the printed one is the same), and the combinators trace, maps,
and invs, which -print lean prints as applications of these functions (see README.md).

Traces are a value followed by a trace (step) or a last value (stop), hence a trace is never empty, and the trace
combinator is a right fold over its dependency. There is a single combinator of each kind over a single dependency:
several dependencies are zipped into a list of tuples, which truncates them to the shortest one, whereas the
dependencies of the combinators of Cuvée have equal lengths, which the lemmas state as hypotheses on the lengths
(lean.Printer.lengths, premises.txt).
-/
namespace TEQ

-- the traces of trace equation systems, the values of a variable at the loop head: the value before an iteration
-- followed by the trace of the remaining iterations (step), or the last value (stop)
inductive Trace (α₀ : Type) where
  | stop (last : α₀) : Trace α₀
  | step (first : α₀) (rest : Trace α₀) : Trace α₀

-- the combinators: the trace of the accumulator, which starts with x and is updated by f with the values of the
-- dependency in turn, a right fold over the dependency, the sequence of the updates of these values, and the
-- invariant of these values
def trace {α β : Type} (x : α) : List β → (α → β → α) → Trace α
  | [], _ => .stop x
  | d :: ds, f => .step x (trace (f x d) ds f)

def maps {β γ : Type} : List β → (β → γ) → List γ
  | [], _ => []
  | d :: ds, f => f d :: maps ds f

def invs {β : Type} : List β → (β → Prop) → Prop
  | [], _ => True
  | d :: ds, φ => φ d ∧ invs ds φ

end TEQ
