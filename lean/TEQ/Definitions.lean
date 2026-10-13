/-
The functions that the modules of the lemma database declare without a body, whose meaning their comments describe
and their lemmas use: a model of each, by hand, which the proofs of the lemmas rely on, so that the lemmas are shown
consistent and true of the described meaning. The generator drops the printed axioms of these functions after checking
their types (DEFINED in scripts/lean/generate.py).
-/
import TEQ.Semantics

open Classical

namespace TEQ

-- teq.dfy: the cut of G on [l, h), the first index of the interval where G fails, h if none (l if the interval is
-- empty); cutFrom G l n searches the n indices from l
noncomputable def cutFrom (G : Int → Prop) (l : Int) : Nat → Int
  | 0 => l
  | n + 1 => if G l then cutFrom G (l + 1) n else l

noncomputable def cut (G : Int → Prop) (l h : Int) : Int :=
  cutFrom G l (h - l).toNat

-- sorted.dfy: a[lo..hi) is nondecreasing
def sorted (a : Int → Int) (lo hi : Int) : Prop :=
  ∀ i j, lo ≤ i → i ≤ j → j < hi → a i ≤ a j

-- a is a permutation of b as a total map on the indices: b read through a bijection of the indices
def perm (a b : Int → Int) : Prop :=
  ∃ f g : Int → Int, (∀ i, g (f i) = i) ∧ (∀ i, f (g i) = i) ∧ ∀ i, a i = b (f i)

-- all of a[lo..mid) are at most all of a[mid..hi)
def partitioned (a : Int → Int) (lo mid hi : Int) : Prop :=
  ∀ i j, lo ≤ i → i < mid → mid ≤ j → j < hi → a i ≤ a j

-- the partition points of a[0..len): the cut of the elements less than y, and of those at most y
noncomputable def lower (ar : Int → Int) (len y : Int) : Int :=
  cut (fun j => ar j < y) 0 len

noncomputable def upper (ar : Int → Int) (len y : Int) : Int :=
  cut (fun j => ar j ≤ y) 0 len

end TEQ
