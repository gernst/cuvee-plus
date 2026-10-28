/-
The part of the semantics of the lemma database of -teq that the printer does not produce: the datatype of traces,
which the generator takes from here (it checks that the printed one is the same), and the combinators trace, maps,
and invs, which -print lean prints as applications of these functions (see README.md).

Traces are a value followed by a trace (step) or a last value (stop), hence a trace is never empty, and the trace
combinator is a right fold over its dependency. There is a single combinator of each kind over a single dependency:
several dependencies are zipped into a list of tuples, which truncates them to the shortest one, whereas the
dependencies of the combinators of Cuvée have equal lengths, which the lemmas state as hypotheses on the lengths
(lean.Printer.lengths, premises.txt).

Multisets (the bags of the core, Dafny's multiset<a>) are the lists up to permutation, the quotient of List α by
List.Perm: the empty multiset, a single element, union, difference, the multiplicity of an element, and submultisets
are lifted from the lists, the difference by erasing the elements of the second list one by one, which cuts off at
zero like the core's (cvc5's bag.difference_subtract), and submultisets compare the multiplicities. The aggregates sum,
parity, max, and min, which the modules declare without a body and characterize by their lemmas, are folds of the
lists, lifted by the proof that the fold does not depend on the order; the generator checks and leaves out their
printed declarations (AGGREGATES of scripts/lean/generate.py).
-/
open Classical

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

-- multisets, the lists up to permutation; -print lean prints the empty multiset as ∅, a single element as {x}, union,
-- difference, and submultisets as +, -, ≤, and the multiplicity m[e] as Bag.count m e
def Bag (α : Type) : Type := Quotient (List.isSetoid α)

namespace Bag

def mk {α : Type} (xs : List α) : Bag α := Quotient.mk _ xs

-- the list without the elements of another one, each erased once per occurrence, hence cut off at zero
noncomputable def diff {α : Type} : List α → List α → List α
  | xs, [] => xs
  | xs, y :: ys => diff (xs.erase y) ys

theorem count_diff {α : Type} (e : α) : ∀ (xs ys : List α), (diff xs ys).count e = xs.count e - ys.count e
  | xs, [] => by simp [diff]
  | xs, y :: ys => by
    rw [diff, count_diff e (xs.erase y) ys, List.count_erase, List.count_cons]
    split <;> omega

instance {α : Type} : EmptyCollection (Bag α) := ⟨mk []⟩

instance {α : Type} : Singleton α (Bag α) := ⟨fun x => mk [x]⟩

instance {α : Type} : Add (Bag α) :=
  ⟨Quotient.lift₂ (fun xs ys => mk (xs ++ ys)) (fun _ _ _ _ h h' => Quotient.sound (List.Perm.append h h'))⟩

noncomputable instance {α : Type} : Sub (Bag α) :=
  ⟨Quotient.lift₂ (fun xs ys => mk (diff xs ys)) (fun _ _ _ _ h h' =>
    Quotient.sound (List.perm_iff_count.2 (fun e => by
      rw [count_diff, count_diff, List.Perm.count_eq h, List.Perm.count_eq h'])))⟩

-- the element x with the multiplicity n, none if it is not positive
noncomputable def make {α : Type} (x : α) (n : Int) : Bag α := mk (List.replicate n.toNat x)

noncomputable def count {α : Type} (m : Bag α) (e : α) : Int :=
  Quotient.lift (fun xs => (xs.count e : Int)) (fun _ _ h => by rw [List.Perm.count_eq h]) m

instance {α : Type} : LE (Bag α) := ⟨fun n m => ∀ e, count n e ≤ count m e⟩

-- the fold of a list by a function whose updates commute does not depend on the order of the list
theorem foldr_perm {α β : Type} (f : α → β → β) (comm : ∀ x y z, f y (f x z) = f x (f y z)) (x : β)
    (xs ys : List α) (h : xs ≈ ys) : xs.foldr f x = ys.foldr f x :=
  List.Perm.foldr_eq' h (fun a _ b _ z => comm a b z) x

end Bag

-- the aggregates, the folds of the elements, from x for the maximum and the minimum
noncomputable def sum : Bag Int → Int :=
  Quotient.lift (fun xs => xs.foldr (fun v s => v + s) 0) (Bag.foldr_perm _ (by intros; omega) 0)

noncomputable def parity : Bag Int → Int :=
  Quotient.lift (fun xs => xs.foldr (fun v s => (if v % 2 = 0 then 1 else -1) + s) 0)
    (Bag.foldr_perm _ (by intros; split <;> split <;> omega) 0)

noncomputable def max (x : Int) : Bag Int → Int :=
  Quotient.lift (fun xs => xs.foldr (fun v m => if m ≤ v then v else m) x)
    (Bag.foldr_perm _ (by intro a b z; by_cases h₁ : z ≤ a <;> by_cases h₂ : z ≤ b <;> by_cases h₃ : a ≤ b <;>
      simp [h₁, h₂, h₃] <;> omega) x)

noncomputable def min (x : Int) : Bag Int → Int :=
  Quotient.lift (fun xs => xs.foldr (fun v m => if m ≤ v then m else v) x)
    (Bag.foldr_perm _ (by intro a b z; by_cases h₁ : z ≤ a <;> by_cases h₂ : z ≤ b <;> by_cases h₃ : a ≤ b <;>
      simp [h₁, h₂, h₃] <;> omega) x)

end TEQ
