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
printed declarations (AGGREGATES of scripts/lean/generate.py). So are the bit operations bitand, bitor, bitxor of C,
which core Lean lacks on integers: Mathlib's Int.land, Int.lor, and Int.xor, two's complement on unbounded integers,
which are associative and commutative by the bits (Bits.ext), and their aggregates band, bor, and bxor, the folds from
all ones (-1) and from zero.

The value in two phases, phases x0 m n F G of counters.dfy, which the module declares without a body, is the trace of
the comment above it, trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case k < m => F(x, k) case m <= k => G(x, k)), over
the iterations 0, ..., n - 1 (iterations, since the counters are defined by the printer); the generator leaves out its
printed declaration as well.

The constant array const v of the prelude, which the printer prints as an application without a declaration, is the
constant function, as arrays are the functions from their keys to their values.
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

-- the bit operations of C on unbounded integers in two's complement, Mathlib's Int.land and Int.lor, which core Lean
-- lacks: a natural is its bits, followed by zeros, and the negative -[m+1] = -m - 1 is the complement of the bits of
-- m, followed by ones; the bits of m not among those of n are ldiff m n
namespace Bits

def ldiff (m n : Nat) : Nat := m ^^^ (m &&& n)

def land : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .ofNat m, .negSucc n => .ofNat (ldiff m n)
  | .negSucc m, .ofNat n => .ofNat (ldiff n m)
  | .negSucc m, .negSucc n => .negSucc (m ||| n)

def lor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ||| n)
  | .ofNat m, .negSucc n => .negSucc (ldiff n m)
  | .negSucc m, .ofNat n => .negSucc (ldiff m n)
  | .negSucc m, .negSucc n => .negSucc (m &&& n)

-- the complement of one operand complements the result
def lxor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ^^^ n)
  | .ofNat m, .negSucc n => .negSucc (m ^^^ n)
  | .negSucc m, .ofNat n => .negSucc (m ^^^ n)
  | .negSucc m, .negSucc n => .ofNat (m ^^^ n)

-- the i-th bit in two's complement
def testBit : Int → Nat → Bool
  | .ofNat m, i => m.testBit i
  | .negSucc m, i => !m.testBit i

theorem testBit_ldiff (m n i : Nat) : (ldiff m n).testBit i = (m.testBit i && !n.testBit i) := by
  simp only [ldiff, Nat.testBit_xor, Nat.testBit_and]
  cases m.testBit i <;> cases n.testBit i <;> rfl

theorem testBit_land (a b : Int) (i : Nat) : testBit (land a b) i = (testBit a i && testBit b i) := by
  cases a <;> cases b <;>
    simp only [land, testBit, testBit_ldiff, Nat.testBit_and, Nat.testBit_or] <;>
    cases Nat.testBit _ i <;> cases Nat.testBit _ i <;> rfl

theorem testBit_lor (a b : Int) (i : Nat) : testBit (lor a b) i = (testBit a i || testBit b i) := by
  cases a <;> cases b <;>
    simp only [lor, testBit, testBit_ldiff, Nat.testBit_and, Nat.testBit_or] <;>
    cases Nat.testBit _ i <;> cases Nat.testBit _ i <;> rfl

theorem testBit_lxor (a b : Int) (i : Nat) : testBit (lxor a b) i = (testBit a i ^^ testBit b i) := by
  cases a <;> cases b <;>
    simp only [lxor, testBit, Nat.testBit_xor] <;>
    cases Nat.testBit _ i <;> cases Nat.testBit _ i <;> rfl

-- integers of the same bits are equal: a natural and a negative number differ at a bit above both
theorem ext {a b : Int} (h : ∀ i, testBit a i = testBit b i) : a = b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact congrArg _ (Nat.eq_of_testBit_eq h)
    | negSucc n =>
      have e := h (m + n)
      simp only [testBit, Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt (Nat.le_add_right m n) Nat.lt_two_pow_self),
        Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt (Nat.le_add_left n m) Nat.lt_two_pow_self)] at e
      contradiction
  | negSucc m =>
    cases b with
    | ofNat n =>
      have e := h (m + n)
      simp only [testBit, Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt (Nat.le_add_right m n) Nat.lt_two_pow_self),
        Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt (Nat.le_add_left n m) Nat.lt_two_pow_self)] at e
      contradiction
    | negSucc n =>
      exact congrArg _ (Nat.eq_of_testBit_eq (fun i => by have := h i; simp only [testBit] at this; simpa using this))

theorem land_comm (a b : Int) : land a b = land b a :=
  ext fun i => by rw [testBit_land, testBit_land, Bool.and_comm]

theorem land_assoc (a b c : Int) : land (land a b) c = land a (land b c) :=
  ext fun i => by rw [testBit_land, testBit_land, testBit_land, testBit_land, Bool.and_assoc]

theorem land_neg_one (a : Int) : land a (-1) = a :=
  ext fun i => by rw [testBit_land]; show (testBit a i && !Nat.testBit 0 i) = _; simp

theorem lor_comm (a b : Int) : lor a b = lor b a :=
  ext fun i => by rw [testBit_lor, testBit_lor, Bool.or_comm]

theorem lor_assoc (a b c : Int) : lor (lor a b) c = lor a (lor b c) :=
  ext fun i => by rw [testBit_lor, testBit_lor, testBit_lor, testBit_lor, Bool.or_assoc]

theorem lor_zero (a : Int) : lor a 0 = a :=
  ext fun i => by rw [testBit_lor]; show (testBit a i || Nat.testBit 0 i) = _; simp

theorem lxor_comm (a b : Int) : lxor a b = lxor b a :=
  ext fun i => by rw [testBit_lxor, testBit_lxor, Bool.xor_comm]

theorem lxor_assoc (a b c : Int) : lxor (lxor a b) c = lxor a (lxor b c) :=
  ext fun i => by rw [testBit_lxor, testBit_lxor, testBit_lxor, testBit_lxor, Bool.xor_assoc]

theorem lxor_zero (a : Int) : lxor a 0 = a :=
  ext fun i => by rw [testBit_lxor]; show (testBit a i ^^ Nat.testBit 0 i) = _; simp

end Bits

-- the bit operations of the C prelude and their aggregates, the folds of the elements from all ones and from zero
def bitand : Int → Int → Int := Bits.land

def bitor : Int → Int → Int := Bits.lor

def bitxor : Int → Int → Int := Bits.lxor

noncomputable def band : Bag Int → Int :=
  Quotient.lift (fun xs => xs.foldr (fun v r => bitand v r) (-1))
    (Bag.foldr_perm _ (fun x y z => by
      show Bits.land y (Bits.land x z) = Bits.land x (Bits.land y z)
      rw [← Bits.land_assoc, Bits.land_comm y x, Bits.land_assoc]) (-1))

noncomputable def bor : Bag Int → Int :=
  Quotient.lift (fun xs => xs.foldr (fun v r => bitor v r) 0)
    (Bag.foldr_perm _ (fun x y z => by
      show Bits.lor y (Bits.lor x z) = Bits.lor x (Bits.lor y z)
      rw [← Bits.lor_assoc, Bits.lor_comm y x, Bits.lor_assoc]) 0)

noncomputable def bxor : Bag Int → Int :=
  Quotient.lift (fun xs => xs.foldr (fun v r => bitxor v r) 0)
    (Bag.foldr_perm _ (fun x y z => by
      show Bits.lxor y (Bits.lxor x z) = Bits.lxor x (Bits.lxor y z)
      rw [← Bits.lxor_assoc, Bits.lxor_comm y x, Bits.lxor_assoc]) 0)

-- the constant array of the prelude, an array is a function from its keys to its values
def const {α β : Type} (v : β) : α → β := fun _ => v

-- the iterations s, s + 1, ... of a loop of t steps, the values of a counter from s by 1 (Proofs.lean: iterations_N)
def iterations (s : Int) : Nat → List Int
  | 0 => []
  | t + 1 => s :: iterations (s + 1) t

-- a value in two phases: the first m iterations update it by F, the others by G
def phases (x0 m n : Int) (F G : Int → Int → Int) : Trace Int :=
  trace x0 (iterations 0 n.toNat) (fun x k => if k < m then F x k else G x k)

end TEQ
