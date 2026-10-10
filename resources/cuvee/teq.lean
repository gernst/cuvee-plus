/-
The semantics of the lemma database of -teq (teq.dfy) in Lean 4, without Mathlib: the datatype of traces, the
functions, which teq.dfy defines by recursion, and the lemmas are printed by
`./Cuvee.sh -print lean resources/cuvee/teq.dfy`, the lemmas as theorems, all of them proved; the combinators are
defined here.

Traces are the datatype of teq.dfy, a value followed by a trace (step) or a last value (stop), hence a trace is
never empty, and the trace combinator is a right fold over its dependency; the naturals and lists of teq.dfy are
those of Lean, arrays are functions. There is a single combinator of each kind, trace, maps, and invs, over a single
dependency: several dependencies are zipped into a list of tuples, which truncates them to the shortest one, whereas
the dependencies of the combinators of Cuvée have equal lengths, which teq.dfy does not state (see TODO.md);
`case φ => e case ψ => f` updates are conditionals (the guards are disjoint and complete).

The statements of the lemmas are those printed by -print lean: for the lemmas that hold for dependencies of equal
length only, the printer adds hypotheses on the lengths (see lean.Printer.lengths): each list-typed variable that is
a dependency of a combinator, also through a function defined by one (stores, selects, sums, ...), or that is read
at the iterations k of a counter, earlier(natural(k), xs), has the length n of the loop, `(hxs : length xs = n)`,
where n is the number of steps of a counter among the dependencies, `⌊counter(_, _, n)⌋`, or a further parameter
`(n : Nat)` of the theorem otherwise, and length is List.length of Lean, declared in teq.dfy with :lean. Lemmas that
hold for indices within the lists only, whose elements are unspecified otherwise, or for complete guards, have these
assumptions as further premises by hand, in the form of requires of teq.dfy, which are to be added there
(earlier_counter, earlier_consts, earlier_selects, earlier_sums, earlier_counts, earlier_prefix, prefix_counter,
prefix_consts, prefix_prefix, occurs_earlier, earlier_stores, current_maxs_earlier, current_mins_earlier, the
completeness of the guards of current_trace_bounded), and the lemmas without a combinator state the length of a list
read at the iterations by hand (occurs_earlier, earlier_not_occurs_prefix, sum_consts_prefix, sum_below_prefix,
earlier_nonneg_prefix, sum_nonneg_prefix). The counterexamples at the end show that
the assumptions are needed.
Check with `lean resources/cuvee/teq.lean` (Lean 4.34).
-/
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace TEQ

-- the constructors of Nat and List, which are those of Lean ({:lean} in teq.dfy)
open Nat (zero succ)
open List (nil cons length)

def integer (n : Nat) : Int :=
  match n with
  | .zero => 0
  | .succ m => integer m + 1

-- the natural number of an integer, zero for those that are not positive
def natural (x : Int) : Nat :=
  if x ≤ 0 then zero else succ (natural (x - 1))
termination_by x.toNat
decreasing_by all_goals omega

-- a value that is not specified, e.g. of the elements outside of a list
axiom unspecified {α : Type} [Inhabited α] : α

-- the type and the functions of Fun.trace, whose type parameters and formals are numbered as there (Fun.formals)

-- the traces of trace equation systems, the values of a variable at the loop head: the value before an iteration
-- followed by the trace of the remaining iterations (step), or the last value (stop)
inductive Trace (α₀ : Type) where
  | stop (last : α₀) : Trace α₀
  | step (first : α₀) (rest : Trace α₀) : Trace α₀

open Trace

-- the last element of a trace
def current {α₀ : Type} [Inhabited α₀] (x₀ : Trace α₀) : α₀ :=
  match x₀ with
  | .stop x => x
  | .step _ xs => current xs

-- all but the last element of a trace, written ⌊X⌋
def butlast {α₀ : Type} [Inhabited α₀] (x₀ : Trace α₀) : List α₀ :=
  match x₀ with
  | .stop _ => nil
  | .step x xs => cons x (butlast xs)

-- counter(i, c, n) is the trace i, i + c, ..., i + n c of n steps
def counter (x₀ : Int) (x₁ : Int) (x₂ : Nat) : Trace Int :=
  match x₂ with
  | .zero => stop x₀
  | .succ m => step x₀ (counter (x₀ + x₁) x₁ m)

-- the elements of lists, unspecified outside of them
def earlier {α₀ : Type} [Inhabited α₀] (x₀ : Nat) (x₁ : List α₀) : α₀ :=
  match x₀, x₁ with
  | _, .nil => unspecified
  | .zero, .cons x _ => x
  | .succ k, .cons _ xs => earlier k xs

-- the first k elements of a list
def «prefix» {α : Type} [Inhabited α] (k : Nat) (xs : List α) : List α :=
  match k, xs with
  | .zero, _ => nil
  | _, .nil => nil
  | .succ m, .cons x ys => cons x («prefix» m ys)

-- whether x occurs in a list, and the index of its last occurrence (unspecified otherwise, zero here)
def occurs {α : Type} [Inhabited α] (x : α) (xs : List α) : Prop :=
  match xs with
  | .nil => False
  | .cons y ys => y = x ∨ occurs x ys

def indexof {α : Type} [Inhabited α] (x : α) (xs : List α) : Nat :=
  match xs with
  | .nil => zero
  | .cons y ys => if occurs x ys then succ (indexof x ys) else zero

-- whether a list has no duplicates
def distincts {α : Type} [Inhabited α] (xs : List α) : Prop :=
  match xs with
  | .nil => True
  | .cons y ys => ¬occurs y ys ∧ distincts ys

-- consts(n, v) is the trace v, ..., v of n steps
def consts {α : Type} [Inhabited α] (n : Nat) (v : α) : Trace α :=
  match n with
  | .zero => stop v
  | .succ m => step v (consts m v)

-- the sum of a list
def sum (values : List Int) : Int :=
  match values with
  | .nil => 0
  | .cons v vs => v + sum vs

-- the parity of a list, the number of even minus the number of odd elements
def parity (values : List Int) : Int :=
  match values with
  | .nil => 0
  | .cons v vs => (if v % 2 = 0 then 1 else -1) + parity vs

-- the number of occurrences of a value in a list
def count {α : Type} [Inhabited α] (e : α) (vs : List α) : Int :=
  match vs with
  | .nil => 0
  | .cons v ws => (if v = e then 1 else 0) + count e ws

-- auxiliary predicates: abstractions of iteration constraints, which lemmas instantiate at witnesses, since a side
-- condition that is an iteration constraint does not terminate; named apart from the predicates that inputs declare
-- with other meanings, which would be identified with them if their signatures agreed

-- the first n values of xs and ys agree
def agree_prefix (n : Nat) (xs : List Int)
                 (ys : List Int) : Prop :=
  match n with
  | .zero => True
  | .succ m => agree_prefix m xs ys ∧ earlier m xs = earlier m ys

-- the first n values of js are all c
def consts_prefix (n : Nat) (c : Int) (js : List Int) : Prop :=
  match n with
  | .zero => True
  | .succ m => consts_prefix m c js ∧ earlier m js = c

-- the first n values of ts exceed their positions
def above_iterations (n : Nat) (ts : List Int) : Prop :=
  match n with
  | .zero => True
  | .succ m => above_iterations m ts ∧ integer m < earlier m ts

-- the first n values of xs are at most b, and nonnegative, for the values chosen in each of n iterations
def below_prefix (n : Nat) (xs : List Int) (b : Int) : Prop :=
  match n with
  | .zero => True
  | .succ m => below_prefix m xs b ∧ earlier m xs ≤ b

def nonneg_prefix (n : Nat) (xs : List Int) : Prop :=
  match n with
  | .zero => True
  | .succ m => nonneg_prefix m xs ∧ 0 ≤ earlier m xs

-- powers, which are not unfolded
def pow (c : Int) (n : Nat) : Int :=
  match n with
  | .zero => 1
  | .succ m => c * pow c m

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

-- naturals: their values as integers, which the arithmetic of the simplifier reasons about, and back

-- auxiliary lemmas of the proofs
-- integer and natural are the conversions of Lean
theorem integer_eq (n : Nat) : integer n = (n : Int) := by
  induction n with
  | zero => rfl
  | succ m ih => rw [integer, ih]; omega

theorem natural_eq (x : Int) : natural x = x.toNat := by
  rw [natural]
  split
  · show (0 : Nat) = x.toNat; omega
  · rw [natural_eq (x - 1)]; show (x - 1).toNat + 1 = x.toNat; omega
termination_by x.toNat
decreasing_by omega

-- the values before the last one of a counter and of consts
theorem butlast_counter_succ (i c : Int) (m : Nat) :
    butlast (counter i c (m + 1)) = i :: butlast (counter (i + c) c m) := rfl

theorem length_butlast_counter (i c : Int) (n : Nat) : (butlast (counter i c n)).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ m ih => simp [butlast_counter_succ, ih]

theorem length_butlast_consts {α : Type} [Inhabited α] (n : Nat) (v : α) :
    (butlast (consts n v)).length = n := by
  induction n with
  | zero => rfl
  | succ m ih => simp [consts, butlast, ih]

-- the first k states of a trace are those of the trace over the first k values
theorem prefix_butlast_trace {α β : Type} [Inhabited α] [Inhabited β] (k : Nat) (x : α) (vs : List β)
    (f : α → β → α) : «prefix» k (butlast (trace x vs f)) = butlast (trace x («prefix» k vs) f) := by
  induction vs generalizing k x with
  | nil => cases k <;> rfl
  | cons v vs ih => cases k with
    | zero => rfl
    | succ m => simp only [trace, butlast, «prefix»]; rw [ih]

theorem prefix_zip {α β : Type} [Inhabited α] [Inhabited β] [Inhabited (α × β)] (k : Nat) (xs : List α)
    (ys : List β) : «prefix» k (List.zip xs ys) = List.zip («prefix» k xs) («prefix» k ys) := by
  induction xs generalizing k ys with
  | nil => cases k <;> simp [«prefix»]
  | cons x xs ih => cases k with
    | zero => simp [«prefix»]
    | succ m => cases ys with
      | nil => simp [«prefix»]
      | cons y ys => simp only [List.zip_cons_cons, «prefix»]; rw [ih]

-- a positive multiple of the step lies beyond the step, in its direction
theorem step_mul (m : Nat) (c : Int) (h : 1 ≤ m) : (0 ≤ c → c ≤ (m : Int) * c) ∧ (c < 0 → (m : Int) * c ≤ c) := by
  constructor
  · intro hc; have := Int.mul_le_mul_of_nonneg_right (show (1 : Int) ≤ m by omega) hc; simpa using this
  · intro hc; have := Int.mul_le_mul_of_nonpos_right (show (1 : Int) ≤ m by omega) (by omega : c ≤ 0); simpa using this

-- the numbers of values of a counter by 1 below m and from m on, in both truth values
theorem count_lt_counter (m i : Int) (n : Nat) :
    count True (maps (butlast (counter i 1 n)) (fun k => k < m)) = max 0 (min (n : Int) (m - i)) ∧
    count False (maps (butlast (counter i 1 n)) (fun k => k < m)) = (n : Int) - max 0 (min (n : Int) (m - i)) := by
  induction n generalizing i with
  | zero => (simp [counter, butlast, maps, count]) <;> omega
  | succ k ih =>
    simp only [butlast_counter_succ, maps, count]
    rw [(ih (i + 1)).1, (ih (i + 1)).2]
    by_cases h : i < m <;> simp [h] <;> omega

theorem count_le_counter (m i : Int) (n : Nat) :
    count True (maps (butlast (counter i 1 n)) (fun k => m ≤ k)) = (n : Int) - max 0 (min (n : Int) (m - i)) ∧
    count False (maps (butlast (counter i 1 n)) (fun k => m ≤ k)) = max 0 (min (n : Int) (m - i)) := by
  induction n generalizing i with
  | zero => (simp [counter, butlast, maps, count]) <;> omega
  | succ k ih =>
    simp only [butlast_counter_succ, maps, count]
    rw [(ih (i + 1)).1, (ih (i + 1)).2]
    by_cases h : m ≤ i <;> simp [h] <;> omega

-- a value that is at least b grows by c in each step of the second phase
theorem current_trace_second_phase (x : Int) (s : Int) (m : Nat) (b c : Int) (hx : b ≤ x) (hc : 0 ≤ c) :
    current (trace x (butlast (counter s 1 m)) (fun x k => if x < b then x + 1 else x + c)) = x + (m : Int) * c := by
  induction m generalizing x s with
  | zero => simp [counter, butlast, trace, current]
  | succ k ih =>
    simp only [butlast_counter_succ, trace, current]
    rw [ite_eq_right (by omega), ih (x + c) (s + 1) (by omega)]
    push_cast; grind

-- a map over a counter shifted by one is the map of the shifted function
theorem maps_counter_shift (s : Int) (m : Nat) (G : Int → Int) :
    maps (butlast (counter (s + 1) 1 m)) G = maps (butlast (counter s 1 m)) (fun k => G (k + 1)) := by
  induction m generalizing s with
  | zero => rfl
  | succ t ih => simp only [butlast_counter_succ, maps]; rw [ih (s + 1)]

-- the sum of G over s, ..., j - 1
theorem sum_counter_succ (s : Int) (t : Nat) (G : Int → Int) :
    sum (maps (butlast (counter s 1 (t + 1))) G) = G s + sum (maps (butlast (counter (s + 1) 1 t)) G) := rfl


-- shifting from s on reads positions that are not written yet, which still hold the initial values
theorem shifts_general (d : Int) (hd : 0 ≤ d) (a : Int → Int) (k : Int) : ∀ (m : Nat) (s : Int) (b : Int → Int),
    (∀ x, s ≤ x → b x = a x) →
    current (trace b (butlast (counter s 1 m)) (fun b k => fun j => if j = k then b (k + d) else b j)) k
      = if s ≤ k ∧ k < s + m then a (k + d) else b k := by
  intro m
  induction m with
  | zero => intro s b _; simp [counter, butlast, trace, current]; omega
  | succ t ih =>
    intro s b hb
    simp only [butlast_counter_succ, trace, current]
    rw [ih (s + 1) _ (by intro x hx; simp [show x ≠ s by omega, hb x (by omega)])]
    rw [hb (s + d) (by omega)]
    push_cast
    by_cases e : k = s
    · subst e; (simp) <;> omega
    · simp [e]; (repeat' split) <;> omega

-- maps that agree on the values of a counter
theorem maps_counter_congr (s : Int) (m : Nat) (f g : Int → Int) (h : ∀ k, s ≤ k ∧ k < s + m → f k = g k) :
    maps (butlast (counter s 1 m)) f = maps (butlast (counter s 1 m)) g := by
  induction m generalizing s with
  | zero => rfl
  | succ t ih =>
    simp only [butlast_counter_succ, maps]
    rw [h s (by omega), ih (s + 1) (by intro k hk; exact h k (by push_cast; omega))]

theorem maps_counter_congr_gen {γ : Type} (s : Int) (m : Nat) (f g : Int → γ) (h : ∀ k, s ≤ k ∧ k < s + m → f k = g k) :
    maps (butlast (counter s 1 m)) f = maps (butlast (counter s 1 m)) g := by
  induction m generalizing s with
  | zero => rfl
  | succ t ih =>
    simp only [butlast_counter_succ, maps]
    rw [h s (by omega), ih (s + 1) (by intro k hk; exact h k (by push_cast; omega))]

-- a counter shifted by d
theorem maps_counter_offset (s d : Int) (m : Nat) (G : Int → Int) :
    maps (butlast (counter (s + d) 1 m)) G = maps (butlast (counter s 1 m)) (fun k => G (k + d)) := by
  induction m generalizing s with
  | zero => rfl
  | succ t ih => simp only [butlast_counter_succ, maps]; rw [← ih (s + 1), show s + d + 1 = s + 1 + d by omega]


theorem natural_integer (n : Nat) : natural (integer n) = n :=
  by simp [natural_eq, integer_eq]

theorem integer_natural (x : Int) : 0 ≤ x → integer (natural x) = x :=
  by intro h; simp [natural_eq, integer_eq]; omega

theorem zero_integer (n : Nat) : n = zero ↔ integer n = 0 :=
  by cases n <;> simp [integer_eq] <;> omega

-- loops whose numbers of iterations have the same value, e.g. N for loops in sequence, iterate equally often
-- (from ss1)
theorem integer_injective (m : Nat) (n : Nat) :
  integer m = integer n ↔ m = n :=
  by simp only [integer_eq]; constructor <;> intro h <;> omega

-- small constants as naturals and back, e.g. the iterations of loops with literal bounds, and indices of reads
-- the natural of a value that is not positive is zero, e.g. the iterations of a loop that does not run
theorem natural_nonpositive (x : Int) : x ≤ 0 → natural x = zero :=
  by intro h; simp [natural_eq]; omega

theorem natural_zero : natural 0 = zero :=
  by simp [natural_eq]

theorem natural_one : natural 1 = succ zero :=
  by simp [natural_eq]

theorem natural_two : natural 2 = succ (succ zero) :=
  by simp [natural_eq]

theorem integer_zero : integer zero = 0 :=
  by rfl

theorem integer_one : integer (succ zero) = 1 :=
  by rfl

theorem integer_two : integer (succ (succ zero)) = 2 :=
  by rfl

-- traces

-- a variable that is increased by c in each iteration is a counter (example 2.3 of the paper)
theorem counter_def (i : Int) (c : Int) (n : Nat) :
  trace i (butlast (counter 0 1 n)) (fun x k => x + c) = counter i c n :=
  by
    suffices h : ∀ (j d : Int), trace i (butlast (counter j d n)) (fun x k => x + c) = counter i c n from h 0 1
    induction n generalizing i with
    | zero => intro j d; rfl
    | succ m ih => intro j d; simp [butlast, counter, trace, ih]

-- a variable that keeps its value in each iteration
theorem consts_def {α : Type} [Inhabited α] (x : α) (i : Int) (c : Int)
                                                  (n : Nat) :
  trace x (butlast (counter i c n)) (fun y v => y) = consts n x :=
  by
    induction n generalizing i with
    | zero => rfl
    | succ m ih => simp [butlast_counter_succ, trace, consts, ih]

-- the trace of the successive stores of the values at the keys into a
def stores {α β : Type} [Inhabited α] [Inhabited β] (a : α → β) (keys : List α)
                                                    (values : List β) : Trace (α → β) :=
  trace
    a
    (List.zip keys values)
    (fun b ⟨k, v⟩ => fun j => if j = k then v else b j)

-- each key is visited once only if they are distinct, hence b[k] is still the initial value a[k],
-- in any context f of the read, which may depend on the other dependencies, but not on the accumulator otherwise
theorem trace_read_initial {α β : Type} [Inhabited α] [Inhabited β] (a : α → β)
                                                                          (keys : List α)
                                                                          (fs : List (β → β))
                                                                          (n : Nat)
                                                                          (hkeys : length keys = n)
                                                                          (hfs : length fs = n) :
  distincts keys
    → trace
      a
      (List.zip keys fs)
      (fun b ⟨k, f⟩ => fun j => if j = k then f (b k) else b j)
      = trace
        a
        (List.zip keys fs)
        (fun b ⟨k, f⟩ => fun j => if j = k then f (a k) else b j) :=
  by
    intro hd
    suffices g : ∀ (b : α → β) (keys : List α) (fs : List (β → β)), distincts keys → (∀ k, occurs k keys → b k = a k) →
        trace b (List.zip keys fs) (fun b ⟨k, f⟩ => fun j => if j = k then f (b k) else b j)
        = trace b (List.zip keys fs) (fun b ⟨k, f⟩ => fun j => if j = k then f (a k) else b j) from
      g a keys fs hd (fun _ _ => rfl)
    intro b keys
    induction keys generalizing b with
    | nil => intro fs _ _; simp [trace]
    | cons k ks ih =>
      intro fs hd hb
      cases fs with
      | nil => simp [trace]
      | cons f fs =>
        simp only [distincts] at hd
        simp only [List.zip_cons_cons, trace]
        rw [hb k (by simp [occurs])]
        congr 1
        apply ih
        · exact hd.2
        · intro k' hk'
          have : k' ≠ k := fun e => hd.1 (e ▸ hk')
          simp [this, hb k' (by simp [occurs, hk'])]

-- the trace of the successive copies a[k] := a[k + d] for the keys, which is modeled for increasing keys and
-- nonnegative offsets only, where the entries read are not yet modified
def shifts (a : Int → Int) (keys : List Int)
           (d : Int) : Trace (Int → Int) :=
  trace a keys (fun b k => fun j => if j = k then b (k + d) else b j)

-- the prefix sums of a sequence starting with an initial value
def sums (x : Int) (values : List Int) : Trace Int :=
  trace x values (fun s v => s + v)

-- the prefix parities starting with an initial value
def parities (x : Int) (values : List Int) : Trace Int :=
  trace x values (fun s v => if v % 2 = 0 then s + 1 else s - 1)

-- the prefix maxima and minima starting with an initial value
def maxs (x : Int) (values : List Int) : Trace Int :=
  trace x values (fun m v => if m < v then v else m)

def mins (x : Int) (values : List Int) : Trace Int :=
  trace x values (fun m v => if v < m then v else m)

-- the number of occurrences of a value, counted from an initial value
def counts {α : Type} [Inhabited α] (x : Int) (e : α)
                                    (vs : List α) : Trace Int :=
  trace x vs (fun y v => if v = e then y + 1 else y)

-- on booleans, the guards are the values themselves; the occurrences of false come first,
-- since the guard b of the other lemma also matches !b, which counts the occurrences of true among the negations
theorem counts_false_def (x : Int) (bs : List Prop) (n : Nat)
                               (hbs : length bs = n) :
  trace x bs (fun y b => if ¬b then y + 1 else y) = counts x False bs :=
  by
    simp only [counts]
    congr 1
    funext y b
    by_cases h : b <;> simp [h]

theorem counts_true_def (x : Int) (bs : List Prop) (n : Nat)
                              (hbs : length bs = n) :
  trace x bs (fun y b => if b then y + 1 else y) = counts x True bs :=
  by
    simp only [counts]
    congr 1
    funext y b
    by_cases h : b <;> simp [h]

-- two cases whose results agree under the guard of the second one, x == c, which the simplifier has substituted
-- into it, are one; the second result is a variable d, since F(c) would be compared literally
-- (from copysome1-1, copysome1-2)
theorem trace_merge_cases_ne (x0 : Int) (n : Nat) (c : Int) (d : Int)
                                   (F : Int → Int) :
  d = F c
    → trace x0 (butlast (counter 0 1 n)) (fun x k => if x ≠ c then F x else d)
      = trace x0 (butlast (counter 0 1 n)) (fun x k => F x) :=
  by
    intro h
    congr 1
    funext x k
    by_cases e : x = c <;> simp [e, h]

-- the same with the guards in the other order
-- (from brs1, brs1f, ifcomp, ms1, ms1f)
theorem trace_merge_cases_eq (x0 : Int) (n : Nat) (c : Int) (d : Int)
                                   (F : Int → Int) :
  d = F c
    → trace x0 (butlast (counter 0 1 n)) (fun x k => if x = c then d else F x)
      = trace x0 (butlast (counter 0 1 n)) (fun x k => F x) :=
  by
    intro h
    congr 1
    funext x k
    by_cases e : x = c <;> simp [e, h]

-- stores at the positions 0, ..., n - 1 of values read from the array itself outside of that range read the initial
-- array
-- (from standard_palindrome_ground)
theorem stores_def_read_unmodified (a0 : Int → Int) (n : Nat)
                                         (hs : List Int) (F : Int → Int → Int)
                                         (hhs : length hs = n) :
  invs (List.zip (butlast (counter 0 1 n)) hs) (fun ⟨k, h⟩ => integer n ≤ F k h)
    → trace
      a0
      (List.zip (butlast (counter 0 1 n)) hs)
      (fun a ⟨k, h⟩ => fun j => if j = k then a (F k h) else a j)
      = stores
        a0
        (butlast (counter 0 1 n))
        (maps
           (List.zip (butlast (counter 0 1 n)) hs)
           (fun ⟨k, h⟩ => a0 (F k h))) :=
  by
    intro hinv
    unfold stores
    suffices g : ∀ (m : Nat) (s : Int) (b : Int → Int) (hs : List Int), (∀ x, integer n ≤ x → b x = a0 x) → s + m ≤ integer n →
        invs (List.zip (butlast (counter s 1 m)) hs) (fun ⟨k, h⟩ => integer n ≤ F k h) →
        trace b (List.zip (butlast (counter s 1 m)) hs) (fun a ⟨k, h⟩ => fun j => if j = k then a (F k h) else a j)
        = trace b (List.zip (butlast (counter s 1 m)) (maps (List.zip (butlast (counter s 1 m)) hs) (fun ⟨k, h⟩ => a0 (F k h))))
            (fun b ⟨k, v⟩ => fun j => @ite _ (j = k) (Classical.propDecidable _) v (b j)) by
      simpa using g n 0 a0 hs (fun _ _ => rfl) (by rw [integer_eq]; omega) hinv
    intro m
    induction m with
    | zero => intro s b hs _ _ _; simp [counter, butlast, trace, maps]
    | succ t ih =>
      intro s b hs hb hE hi
      cases hs with
      | nil => simp [butlast_counter_succ, trace, maps]
      | cons h0 hs =>
        simp only [butlast_counter_succ, List.zip_cons_cons, invs, maps, trace] at hi ⊢
        rw [hb (F s h0) hi.1]
        congr 1
        apply ih (s + 1) _ hs _ (by push_cast at hE; omega) hi.2
        intro x hx
        simp [show x ≠ s by push_cast at hE; omega, hb x hx]

-- maps

theorem maps_const {α : Type} [Inhabited α] (x : α) (i : Int) (c : Int)
                                                  (n : Nat) :
  maps (butlast (counter i c n)) (fun v => x) = butlast (consts n x) :=
  by
    induction n generalizing i with
    | zero => rfl
    | succ m ih => simp [butlast_counter_succ, maps, consts, butlast, ih]

theorem maps_earlier {α : Type} [Inhabited α] (n : Nat) (xs : List α)
                                                    (hxs : length xs = n) :
  maps (butlast (counter 0 1 n)) (fun k => earlier (natural k) xs) = xs :=
  by
    subst hxs
    have gen : ∀ (s : Int) (xs : List α),
        maps (butlast (counter s 1 xs.length)) (fun k => earlier (natural (k - s)) xs) = xs := by
      intro s xs
      induction xs generalizing s with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.length_cons, butlast_counter_succ, maps]
        have hd : natural (s - s) = zero := by simp [natural_eq]
        have hk : ∀ k, s + 1 ≤ k ∧ k < s + 1 + (xs.length : Int) →
            earlier (natural (k - s)) (x :: xs) = earlier (natural (k - (s + 1))) xs := by
          intro k hk
          rw [natural, ite_eq_right (by omega : ¬(k - s ≤ 0))]
          simp only [earlier]
          congr 2
          omega
        rw [hd, maps_counter_congr_gen (s + 1) xs.length _ _ hk, ih (s + 1)]
        rfl
    have := gen 0 xs
    simpa using this

theorem maps_counter_affine (a : Int) (b : Int) (i : Int) (c : Int)
                                  (n : Nat) :
  maps (butlast (counter i c n)) (fun v => a + b * v)
    = butlast (counter (a + b * i) (b * c) n) :=
  by
    induction n generalizing i with
    | zero => rfl
    | succ m ih =>
      simp only [butlast_counter_succ, maps, ih]
      rw [show a + b * (i + c) = a + b * i + b * c by grind]

-- the values of a at the keys
def selects {α β : Type} [Inhabited α] [Inhabited β] (a : α → β) (keys : List α) : List β :=
  maps keys (fun k => a k)

-- auxiliary lemmas for the lemmas that hold for dependencies of equal length only (see TODO.md): the lengths of zipped
-- dependencies and of prefixes, the iteration constraints over a counter and over the lists zipped with it as
-- statements over the positions, maps over zipped lists, reads of earlier states of a trace, monotone traces,
-- and the auxiliary predicates as statements over the positions
theorem length_zip_eq {α β : Type} (xs : List α) (ys : List β) (n : Nat) (hxs : xs.length = n)
    (hys : ys.length = n) : (List.zip xs ys).length = n := by
  rw [List.length_zip, hxs, hys, Nat.min_self]

theorem length_prefix {α : Type} [Inhabited α] (k : Nat) (xs : List α) (h : k ≤ xs.length) :
    («prefix» k xs).length = k := by
  induction xs generalizing k with
  | nil => cases k with
    | zero => rfl
    | succ j => simp at h
  | cons x xs ih => cases k with
    | zero => rfl
    | succ j => simp only [«prefix», List.length_cons]; rw [ih j (by simp at h; omega)]

theorem invs_counter_step_forall (s : Int) (d : Int) (m : Nat) (G : Int → Prop) :
    invs (butlast (counter s d m)) G ↔ ∀ j : Nat, j < m → G (s + j * d) := by
  induction m generalizing s with
  | zero => simp [counter, butlast, invs]
  | succ t ih =>
    simp only [butlast_counter_succ, invs]
    rw [ih (s + d)]
    constructor
    · intro ⟨h0, hrest⟩ j hj
      cases j with
      | zero => simpa using h0
      | succ u =>
        have := hrest u (by omega)
        rw [show s + ((u + 1 : Nat) : Int) * d = s + d + (u : Int) * d by push_cast; rw [Int.add_mul, Int.one_mul]; omega]
        exact this
    · intro h
      constructor
      · simpa using h 0 (by omega)
      · intro u hu
        have := h (u + 1) (by omega)
        rw [show s + ((u + 1 : Nat) : Int) * d = s + d + (u : Int) * d by push_cast; rw [Int.add_mul, Int.one_mul]; omega] at this
        exact this

theorem invs_counter_forall (s : Int) (m : Nat) (G : Int → Prop) :
    invs (butlast (counter s 1 m)) G ↔ ∀ i : Nat, i < m → G (s + i) := by
  rw [invs_counter_step_forall]; simp only [Int.mul_one]

theorem invs_zip_counter (s : Int) (m : Nat) (ts : List Int) (hts : ts.length = m) (P : Int → Int → Prop) :
    invs (List.zip (butlast (counter s 1 m)) ts) (fun ⟨k, t⟩ => P k t)
      ↔ ∀ i : Nat, i < m → P (s + i) (earlier i ts) := by
  induction m generalizing s ts with
  | zero =>
    cases ts with
    | nil => simp [counter, butlast, invs]
    | cons t ts => simp at hts
  | succ n ih =>
    cases ts with
    | nil => simp at hts
    | cons t ts =>
      rw [butlast_counter_succ, List.zip_cons_cons]
      simp only [invs]
      rw [ih (s + 1) ts (by simp at hts; omega)]
      constructor
      · intro ⟨h0, hrest⟩ i hi
        cases i with
        | zero => simpa [earlier] using h0
        | succ j =>
          have := hrest j (by omega)
          rw [show s + ((j + 1 : Nat) : Int) = s + 1 + (j : Int) by push_cast; omega]
          simpa [earlier] using this
      · intro h
        constructor
        · simpa [earlier] using h 0 (by omega)
        · intro i hi
          have := h (i + 1) (by omega)
          rw [show s + ((i + 1 : Nat) : Int) = s + 1 + (i : Int) by push_cast; omega] at this
          simpa [earlier] using this

theorem invs_zip3_last (xs ys zs : List Int) (P : Int → Prop) (h1 : xs.length = ys.length)
    (h2 : ys.length = zs.length) :
    invs (List.zip xs (List.zip ys zs)) (fun ⟨x, y, z⟩ => P z) ↔ invs zs P := by
  induction xs generalizing ys zs with
  | nil => cases zs with
    | nil => simp [invs]
    | cons z zs => simp at h1 h2; omega
  | cons x xs ih =>
    cases ys with
    | nil => simp at h1
    | cons y ys => cases zs with
      | nil => simp at h2
      | cons z zs =>
        simp only [List.zip_cons_cons, invs]
        rw [ih ys zs (by simp at h1; omega) (by simp at h2; omega)]

theorem invs_zip3_middle (xs ys zs : List Int) (P : Int → Prop) (h1 : xs.length = ys.length)
    (h2 : ys.length = zs.length) :
    invs (List.zip xs (List.zip ys zs)) (fun ⟨x, y, z⟩ => P y) ↔ invs ys P := by
  induction xs generalizing ys zs with
  | nil => cases ys with
    | nil => simp [invs]
    | cons y ys => simp at h1
  | cons x xs ih =>
    cases ys with
    | nil => simp at h1
    | cons y ys => cases zs with
      | nil => simp at h2
      | cons z zs =>
        simp only [List.zip_cons_cons, invs]
        rw [ih ys zs (by simp at h1; omega) (by simp at h2; omega)]

theorem invs_zip3_drop_middle (xs ys zs : List Int) (P : Int → Int → Prop) (h1 : xs.length = ys.length)
    (h2 : ys.length = zs.length) :
    invs (List.zip xs (List.zip ys zs)) (fun ⟨x, y, z⟩ => P x z) ↔ invs (List.zip xs zs) (fun ⟨x, z⟩ => P x z) := by
  induction xs generalizing ys zs with
  | nil => simp [invs]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h1
    | cons y ys => cases zs with
      | nil => simp at h2
      | cons z zs =>
        simp only [List.zip_cons_cons, invs]
        rw [ih ys zs (by simp at h1; omega) (by simp at h2; omega)]

theorem maps_zip_fst {α β γ : Type} (xs : List α) (ys : List β) (G : α → γ) (h : xs.length = ys.length) :
    maps (List.zip xs ys) (fun ⟨x, y⟩ => G x) = maps xs G := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.zip_cons_cons, maps]
      rw [ih ys (by simp at h; omega)]

theorem length_butlast_trace {α β : Type} [Inhabited α] (x : α) (ds : List β) (f : α → β → α) :
    (butlast (trace x ds f)).length = ds.length := by
  induction ds generalizing x with
  | nil => rfl
  | cons d ds ih => simp only [trace, butlast, List.length_cons]; rw [ih]

-- the j-th state of a trace is the result of the first j updates
theorem earlier_butlast_trace {α β : Type} [Inhabited α] [Inhabited β] (j : Nat) (x : α) (ds : List β) (f : α → β → α)
    (h : j < ds.length) : earlier j (butlast (trace x ds f)) = current (trace x («prefix» j ds) f) := by
  induction ds generalizing j x with
  | nil => simp at h
  | cons d ds ih =>
    cases j with
    | zero => simp [trace, butlast, earlier, «prefix», current]
    | succ i =>
      simp only [trace, butlast, earlier, «prefix», current]
      exact ih i (f x d) (by simp at h; omega)

-- a trace whose updates do not decrease its value
theorem trace_mono {β : Type} (x : Int) (ps : List β) (f : Int → β → Int) (h : ∀ x p, x ≤ f x p) :
    x ≤ current (trace x ps f) := by
  induction ps generalizing x with
  | nil => simp [trace, current]
  | cons p ps ih => simp only [trace, current]; exact Int.le_trans (h x p) (ih (f x p))

-- a key that is not stored keeps its value
theorem current_stores_not_occurs {α β : Type} [Inhabited α] [Inhabited β] (b : α → β) (ks : List α)
    (vs : List β) (k : α) (h : ¬occurs k ks) : current (stores b ks vs) k = b k := by
  induction ks generalizing b vs with
  | nil => rfl
  | cons k' ks ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [occurs, not_or] at h
      have e : stores b (k' :: ks) (v :: vs) = .step b (stores (fun j => if j = k' then v else b j) ks vs) := rfl
      rw [e]
      simp only [current]
      rw [ih _ vs h.2]
      exact ite_eq_right (fun e => h.1 e.symm)

theorem indexof_lt_length {α : Type} [Inhabited α] (k : α) (ks : List α) (h : occurs k ks) :
    indexof k ks < ks.length := by
  induction ks with
  | nil => simp [occurs] at h
  | cons k' ks ih =>
    simp only [indexof, List.length_cons]
    split
    · next h' => have := ih h'; omega
    · exact Nat.succ_pos _

-- the sign of a multiple of a natural number
theorem nat_mul_sign (t : Nat) (d : Int) : (0 ≤ d → 0 ≤ (t : Int) * d) ∧ (d < 0 → (t : Int) * d ≤ 0) := by
  constructor
  · intro hd; exact Int.mul_nonneg (by omega) hd
  · intro hd
    have := Int.mul_le_mul_of_nonneg_left (show d ≤ 0 by omega) (show (0 : Int) ≤ t by omega)
    simpa using this

-- a lower bound of the values of a counter with an arbitrary step holds in all iterations iff it holds at both ends
theorem invs_counter_positive (i : Int) (d : Int) (n : Nat) (c : Int) :
    invs (butlast (counter i d n)) (fun x => 0 < x + c)
      ↔ n = zero ∨ 0 < i + c ∧ 0 < i + (integer n - 1) * d + c := by
  rw [invs_counter_step_forall, integer_eq]
  constructor
  · intro h
    cases n with
    | zero => exact Or.inl rfl
    | succ m =>
      refine Or.inr ⟨by simpa using h 0 (by omega), ?_⟩
      have := h m (by omega)
      push_cast
      simp only [Int.add_sub_cancel]
      exact this
  · intro h j hj
    rcases h with h | ⟨h1, h2⟩
    · subst h; exact absurd hj (Nat.not_lt_zero j)
    · have hm := nat_mul_sign j d
      by_cases hd : 0 ≤ d
      · have := hm.1 hd; omega
      · have hle : ((n : Int) - 1) * d ≤ (j : Int) * d :=
          Int.mul_le_mul_of_nonpos_right (by omega) (by omega)
        omega

theorem agree_prefix_forall (n : Nat) (xs ys : List Int) :
    agree_prefix n xs ys ↔ ∀ i : Nat, i < n → earlier i xs = earlier i ys := by
  induction n with
  | zero => simp [agree_prefix]
  | succ m ih =>
    simp only [agree_prefix]
    rw [ih]
    constructor
    · intro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
      · exact h1 i h
      · subst h; exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h m (by omega)⟩

theorem above_iterations_forall (n : Nat) (ts : List Int) :
    above_iterations n ts ↔ ∀ i : Nat, i < n → integer i < earlier i ts := by
  induction n with
  | zero => simp [above_iterations]
  | succ m ih =>
    simp only [above_iterations]
    rw [ih]
    constructor
    · intro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
      · exact h1 i h
      · subst h; exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h m (by omega)⟩

theorem consts_prefix_forall (n : Nat) (c : Int) (js : List Int) :
    consts_prefix n c js ↔ ∀ i : Nat, i < n → earlier i js = c := by
  induction n with
  | zero => simp [consts_prefix]
  | succ m ih =>
    simp only [consts_prefix]
    rw [ih]
    constructor
    · intro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
      · exact h1 i h
      · subst h; exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h m (by omega)⟩

theorem below_prefix_forall (n : Nat) (xs : List Int) (b : Int) :
    below_prefix n xs b ↔ ∀ i : Nat, i < n → earlier i xs ≤ b := by
  induction n with
  | zero => simp [below_prefix]
  | succ m ih =>
    simp only [below_prefix]
    rw [ih]
    constructor
    · intro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
      · exact h1 i h
      · subst h; exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h m (by omega)⟩

theorem nonneg_prefix_forall (n : Nat) (xs : List Int) :
    nonneg_prefix n xs ↔ ∀ i : Nat, i < n → 0 ≤ earlier i xs := by
  induction n with
  | zero => simp [nonneg_prefix]
  | succ m ih =>
    simp only [nonneg_prefix]
    rw [ih]
    constructor
    · intro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
      · exact h1 i h
      · subst h; exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h m (by omega)⟩

-- the sum of a list of nonnegative values is nonnegative
theorem sum_nonneg_forall (xs : List Int) (h : ∀ i : Nat, i < xs.length → 0 ≤ earlier i xs) : 0 ≤ sum xs := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih =>
    simp only [sum]
    have h0 : 0 ≤ x := by simpa [earlier] using h 0 (by simp)
    have := ih (fun i hi => by simpa [earlier] using h (i + 1) (by simp; omega))
    omega

theorem not_occurs_prefix_forall (n : Nat) (xs : List Int) (e : Int) (hxs : xs.length = n) :
    ¬occurs e («prefix» n xs) ↔ ∀ i : Nat, i < n → earlier i xs ≠ e := by
  induction xs generalizing n with
  | nil =>
    subst hxs
    simp [«prefix», occurs]
  | cons x xs ih =>
    cases n with
    | zero => simp at hxs
    | succ m =>
      simp only [«prefix», occurs, not_or]
      rw [ih m (by simp at hxs; omega)]
      constructor
      · intro ⟨h1, h2⟩ i hi
        cases i with
        | zero => simpa [earlier] using h1
        | succ j => simpa [earlier] using h2 j (by omega)
      · intro h
        exact ⟨by simpa [earlier] using h 0 (by omega), fun i hi => by simpa [earlier] using h (i + 1) (by omega)⟩

-- invs

theorem invs_const (b : Prop) (i : Int) (c : Int) (n : Nat) :
  invs (butlast (counter i c n)) (fun v => b) ↔ n = zero ∨ b :=
  by
    induction n generalizing i with
    | zero => simp [invs, counter, butlast]
    | succ m ih => simp [butlast_counter_succ, invs, ih]; grind

theorem invs_counter_lower (m : Int) (i : Int) (c : Int) (n : Nat) :
  invs (butlast (counter i c n)) (fun k => m ≤ k)
    ↔ n = zero ∨ m ≤ i ∧ m ≤ i + (integer n - 1) * c :=
  by
    induction n generalizing i with
    | zero => simp [counter, butlast, invs]
    | succ m ih =>
      simp only [butlast_counter_succ, invs, ih, integer_eq]
      cases m with
      | zero => (simp) <;> omega
      | succ m' =>
        have := step_mul (m' + 1) c (by omega)
        simp only [Nat.succ_ne_zero, false_or]
        push_cast at *
        constructor
        · intro ⟨h1, h2, h3⟩; constructor <;> grind
        · intro ⟨h1, h2⟩; refine ⟨h1, ?_, ?_⟩ <;> grind

-- an upper bound m that is nonnegative holds for all values of the counter by 1 from 0 iff it holds for the number of
-- its steps: a counter of an inner loop, whose bound is nonnegative by the precondition, where the disjunction of the
-- general lemma below, with the case of no iteration, is not split in the context of a combinator
-- (from examples/dafny/sorting/nested_sum.dfy)
theorem invs_counter_upper_nonnegative (m : Int) (n : Nat) :
  0 ≤ m → (invs (butlast (counter 0 1 n)) (fun k => k < m) ↔ integer n ≤ m) :=
  by
    intro hm
    rw [invs_counter_forall, integer_eq]
    constructor
    · intro h
      cases n with
      | zero => simpa using hm
      | succ t => have := h t (by omega); simp at this; push_cast; omega
    · intro h i hi; simp; omega

theorem invs_counter_upper (m : Int) (i : Int) (c : Int) (n : Nat) :
  invs (butlast (counter i c n)) (fun k => k < m)
    ↔ n = zero ∨ i < m ∧ i + (integer n - 1) * c < m :=
  by
    induction n generalizing i with
    | zero => simp [counter, butlast, invs]
    | succ m ih =>
      simp only [butlast_counter_succ, invs, ih, integer_eq]
      cases m with
      | zero => (simp) <;> omega
      | succ m' =>
        have := step_mul (m' + 1) c (by omega)
        simp only [Nat.succ_ne_zero, false_or]
        push_cast at *
        constructor
        · intro ⟨h1, h2, h3⟩; constructor <;> grind
        · intro ⟨h1, h2⟩; refine ⟨h1, ?_, ?_⟩ <;> grind

-- a counter by 1 or -1 avoids m if m lies outside of its range, e.g. for loops i != N
theorem invs_counter_ne_up (m : Int) (i : Int) (n : Nat) :
  invs (butlast (counter i 1 n)) (fun k => k ≠ m) ↔ m < i ∨ i + integer n ≤ m :=
  by
    induction n generalizing i with
    | zero => simp [counter, butlast, invs, integer]; omega
    | succ m ih => simp only [butlast_counter_succ, invs, ih, integer_eq]; omega

theorem invs_counter_ne_down (m : Int) (i : Int) (n : Nat) :
  invs (butlast (counter i (-1) n)) (fun k => k ≠ m) ↔ i < m ∨ m ≤ i - integer n :=
  by
    induction n generalizing i with
    | zero => simp [counter, butlast, invs, integer]; omega
    | succ m ih => simp only [butlast_counter_succ, invs, ih, integer_eq]; omega

-- a lower bound of the values x of a counter with an arbitrary step holds in all iterations iff it holds at both
-- ends, since the values are linear; for a counter as the third of three dependencies, with the bound as 0 < x + c,
-- since b < x does not match k < x + n (see TODO.md)
-- (from benchmark04_conjunctive, benchmark09_conjunctive)
theorem invs_counter_positive_last (i : Int) (d : Int) (n : Nat) (c : Int)
                                         (hs : List Int) (gs : List Int)
                                         (hhs : length hs = n)
                                         (hgs : length gs = n) :
  invs
    (List.zip hs (List.zip gs (butlast (counter i d n))))
    (fun ⟨h, g, x⟩ => 0 < x + c)
    ↔ n = zero ∨ 0 < i + c ∧ 0 < i + (integer n - 1) * d + c :=
  by
    exact (invs_zip3_last hs gs _ (fun x => 0 < x + c) (by rw [hhs, hgs]) (by rw [hgs, length_butlast_counter])).trans
      (invs_counter_positive i d n c)

-- the same for a counter as the second of three dependencies
-- (from benchmark09_conjunctive)
theorem invs_counter_positive_middle (i : Int) (d : Int) (n : Nat)
                                           (c : Int) (hs : List Int)
                                           (gs : List Int) (hhs : length hs = n)
                                           (hgs : length gs = n) :
  invs
    (List.zip hs (List.zip (butlast (counter i d n)) gs))
    (fun ⟨h, x, g⟩ => 0 < x + c)
    ↔ n = zero ∨ 0 < i + c ∧ 0 < i + (integer n - 1) * d + c :=
  by
    exact (invs_zip3_middle hs _ gs (fun x => 0 < x + c) (by rw [hhs, length_butlast_counter]) (by rw [hgs, length_butlast_counter])).trans
      (invs_counter_positive i d n c)

-- an iteration constraint that is a negated disjunction, as the test of a break, is two of them
-- (from benchmark09_conjunctive)
theorem invs_not_or (hs : List Int) (gs : List Int) (fs : List Int)
                          (P : Int → Int → Int → Prop)
                          (Q : Int → Int → Int → Prop) (n : Nat)
                          (hhs : length hs = n) (hgs : length gs = n)
                          (hfs : length fs = n) :
  invs (List.zip hs (List.zip gs fs)) (fun ⟨h, g, f⟩ => ¬(P h g f ∨ Q h g f))
    ↔ invs (List.zip hs (List.zip gs fs)) (fun ⟨h, g, f⟩ => ¬P h g f)
      ∧ invs (List.zip hs (List.zip gs fs)) (fun ⟨h, g, f⟩ => ¬Q h g f) :=
  by
    induction (List.zip hs (List.zip gs fs)) with
    | nil => simp [invs]
    | cons p ps ih => obtain ⟨h, g, f⟩ := p; simp only [invs] at *; rw [ih]; grind

-- two sequences that are equal at the iterations 0, ..., n - 1 agree there
-- (from standard_compare_ground)
theorem agree_prefix_def (n : Nat) (xs : List Int) (ys : List Int)
                               (hs : List Int) (hhs : length hs = n)
                               (hxs : length xs = n) (hys : length ys = n) :
  invs
    (List.zip (butlast (counter 0 1 n)) hs)
    (fun ⟨k, h⟩ => earlier (natural k) xs = earlier (natural k) ys)
    ↔ agree_prefix n xs ys :=
  by
    rw [agree_prefix_forall]
    refine (invs_zip_counter 0 n hs hhs (fun k h => earlier (natural k) xs = earlier (natural k) ys)).trans ?_
    simp [natural_eq]

-- a search: the elements before the exit n differ from e, i.e., e does not occur in the prefix of length n
-- (from standard_find_ground-1)
theorem not_occurs_prefix_def (n : Nat) (e : Int) (xs : List Int)
                                    (hs : List Int) (hhs : length hs = n)
                                    (hxs : length xs = n) :
  invs
    (List.zip (butlast (counter 0 1 n)) hs)
    (fun ⟨k, h⟩ => earlier (natural k) xs ≠ e)
    ↔ ¬occurs e («prefix» n xs) :=
  by
    rw [not_occurs_prefix_forall n xs e hxs]
    refine (invs_zip_counter 0 n hs hhs (fun k h => earlier (natural k) xs ≠ e)).trans ?_
    simp [natural_eq]

-- the same for reads of an array at the positions of a counter: x does not occur among the values read there
-- (from lsearch)
theorem not_occurs_selects_def (a : Int → Int) (x : Int) (i : Int)
                                     (n : Nat) :
  invs (butlast (counter i 1 n)) (fun k => a k ≠ x)
    ↔ ¬occurs x (selects a (butlast (counter i 1 n))) :=
  by
    induction n generalizing i with
    | zero => simp [counter, butlast, invs, selects, maps, occurs]
    | succ m ih =>
      simp only [selects] at ih ⊢
      simp only [butlast_counter_succ, invs, maps, occurs]
      rw [ih]
      grind

-- the values of the iterations exceed the iterations
-- (from simple_array_index_value_2)
theorem above_iterations_def (n : Nat) (ts : List Int) (hs : List Int)
                                   (hhs : length hs = n) (hts : length ts = n) :
  invs
    (List.zip (butlast (counter 0 1 n)) (List.zip hs ts))
    (fun ⟨k, h, t⟩ => k < t)
    ↔ above_iterations n ts :=
  by
    rw [above_iterations_forall]
    refine (invs_zip3_drop_middle _ hs ts (fun k t => k < t) (by rw [length_butlast_counter, hhs]) (by rw [hhs, hts])).trans ?_
    refine (invs_zip_counter 0 n ts hts (fun k t => k < t)).trans ?_
    simp [integer_eq]

-- the values of a sequence at the iterations 0, ..., n - 1 are all c, e.g. the final values of an inner counter
-- (from nested_sum)
theorem consts_prefix_def (n : Nat) (c : Int) (js : List Int)
                                (hs : List Int) (hhs : length hs = n)
                                (hjs : length js = n) :
  invs
    (List.zip (butlast (counter 0 1 n)) hs)
    (fun ⟨k, h⟩ => earlier (natural k) js = c)
    ↔ consts_prefix n c js :=
  by
    rw [consts_prefix_forall]
    refine (invs_zip_counter 0 n hs hhs (fun k h => earlier (natural k) js = c)).trans ?_
    simp [natural_eq]

-- butlast

-- a trace of n steps has n values before its last one, hence none if and only if n is zero
-- (from flag_loopdep)
theorem butlast_counter_nil (i : Int) (c : Int) (n : Nat) :
  butlast (counter i c n) = nil ↔ n = zero :=
  by cases n <;> simp [counter, butlast]

theorem butlast_consts_nil {α : Type} [Inhabited α] (n : Nat) (v : α) :
  butlast (consts n v) = nil ↔ n = zero :=
  by cases n <;> simp [consts, butlast]

-- current

theorem current_counter (i : Int) (c : Int) (n : Nat) :
  current (counter i c n) = i + integer n * c :=
  by
    induction n generalizing i with
    | zero => simp [counter, current, integer]
    | succ m ih => simp [counter, current, ih, integer]; grind

theorem current_trace_constant {α : Type} [Inhabited α] (x : α) (y : α)
                                                              (i : Int)
                                                              (c : Int)
                                                              (n : Nat) :
  current (trace x (butlast (counter i c n)) (fun z v => y))
    = (if n = zero then x else y) :=
  by
    cases n with
    | zero => simp [counter, butlast, trace, current]
    | succ m =>
      simp only [butlast_counter_succ, trace, current]
      simp
      induction m generalizing i with
      | zero => rfl
      | succ k ih => simp [butlast_counter_succ, trace, current, ih]

theorem current_consts {α : Type} [Inhabited α] (n : Nat) (x : α) :
  current (consts n x) = x :=
  by
    induction n with
    | zero => rfl
    | succ m ih => simp [consts, current, ih]

theorem current_trace_add_at {α : Type} [Inhabited α] (a : α → Int)
                                                            (k : α)
                                                            (values : List Int)
                                                            (n : Nat)
                                                            (hvalues : length values = n) :
  current (trace a values (fun b v => fun j => if j = k then b k + v else b j))
    = (fun j => if j = k then a k + sum values else a j) :=
  by
    clear hvalues n
    induction values generalizing a with
    | nil => funext j; simp [trace, current, sum]; intro h; rw [h]
    | cons v vs ih =>
      simp only [trace, current, sum]
      rw [ih]
      funext j
      by_cases h : j = k <;> simp [h]; omega

theorem current_sums (x : Int) (values : List Int) (n : Nat)
                           (hvalues : length values = n) :
  current (sums x values) = x + sum values :=
  by
    clear hvalues n
    induction values generalizing x with
    | nil => simp [sums, trace, current, sum]
    | cons v vs ih => simp [sums, trace, current, sum] at *; rw [ih]; omega

theorem current_parities (x : Int) (values : List Int) (n : Nat)
                               (hvalues : length values = n) :
  current (parities x values) = x + parity values :=
  by
    clear hvalues n
    induction values generalizing x with
    | nil => simp [parities, trace, current, parity]
    | cons v vs ih => simp only [parities, trace, current, parity] at *; rw [ih]; split <;> omega

theorem current_maxs_counter (x : Int) (i : Int) (c : Int) (n : Nat) :
  current (maxs x (butlast (counter i c n)))
    = (if n = zero then x else max x (max i (i + (integer n - 1) * c))) :=
  by
    suffices h : ∀ x i, current (maxs x (butlast (counter i c n))) = if n = zero then x else max x (max i (i + (integer n - 1) * c)) from h x i
    induction n with
    | zero => intro x i; simp [counter, butlast, maxs, trace, current]
    | succ m ih =>
      intro x i
      simp only [maxs] at *
      simp only [butlast_counter_succ, trace, current, ih, integer_eq]
      cases m with
      | zero => simp [counter, butlast, trace, current]; grind
      | succ m' => have := step_mul (m' + 1) c (by omega); simp; push_cast at *; grind

theorem current_maxs_consts (x : Int) (y : Int) (n : Nat) :
  current (maxs x (butlast (consts n y))) = (if n = zero then x else max x y) :=
  by
    cases n with
    | zero => simp [consts, butlast, maxs, trace, current]
    | succ m =>
      simp only [ite_eq_right (Nat.succ_ne_zero m)]
      simp only [maxs, consts, butlast, trace, current]
      induction m generalizing x with
      | zero => simp [consts, butlast, trace, current]; grind
      | succ k ih => simp only [consts, butlast, trace, current]; rw [ih]; grind

theorem current_mins_counter (x : Int) (i : Int) (c : Int) (n : Nat) :
  current (mins x (butlast (counter i c n)))
    = (if n = zero then x else min x (min i (i + (integer n - 1) * c))) :=
  by
    suffices h : ∀ x i, current (mins x (butlast (counter i c n))) = if n = zero then x else min x (min i (i + (integer n - 1) * c)) from h x i
    induction n with
    | zero => intro x i; simp [counter, butlast, mins, trace, current]
    | succ m ih =>
      intro x i
      simp only [mins] at *
      simp only [butlast_counter_succ, trace, current, ih, integer_eq]
      cases m with
      | zero => simp [counter, butlast, trace, current]; grind
      | succ m' => have := step_mul (m' + 1) c (by omega); simp; push_cast at *; grind

theorem current_mins_consts (x : Int) (y : Int) (n : Nat) :
  current (mins x (butlast (consts n y))) = (if n = zero then x else min x y) :=
  by
    cases n with
    | zero => simp [consts, butlast, mins, trace, current]
    | succ m =>
      simp only [ite_eq_right (Nat.succ_ne_zero m)]
      simp only [mins, consts, butlast, trace, current]
      induction m generalizing x with
      | zero => simp [consts, butlast, trace, current]; grind
      | succ k ih => simp only [consts, butlast, trace, current]; rw [ih]; grind

theorem current_counts {α : Type} [Inhabited α] (x : Int) (e : α)
                                                      (vs : List α) (n : Nat)
                                                      (hvs : length vs = n) :
  current (counts x e vs) = x + count e vs :=
  by
    clear hvs n
    induction vs generalizing x with
    | nil => simp [counts, trace, current, count]
    | cons v ws ih => simp only [counts, trace, current, count] at *; rw [ih]; split <;> omega

-- a counter in two phases: by 1 up to the bound b, from an initial value up to b, then by c >= 0, which keeps it
-- at least b
-- (from Mono1_1-2, phases_1-1, phases_1-2)
theorem current_trace_two_phases (x0 : Int) (n : Nat) (b : Int)
                                       (c : Int) :
  x0 ≤ b ∧ 0 ≤ c
    → current
      (trace
         x0
         (butlast (counter 0 1 n))
         (fun x k => if x < b then x + 1 else x + c))
      = (if integer n ≤ b - x0 then
           x0 + integer n
         else
           b + (integer n - (b - x0)) * c) :=
  by
    intro ⟨hb, hc⟩
    rw [integer_eq]
    suffices h : ∀ s x, x ≤ b → current (trace x (butlast (counter s 1 n)) (fun x k => if x < b then x + 1 else x + c))
        = (if (n : Int) ≤ b - x then x + n else b + ((n : Int) - (b - x)) * c) from h 0 x0 hb
    induction n with
    | zero => intro s x hx; (simp [counter, butlast, trace, current]) <;> omega
    | succ m ih =>
      intro s x hx
      simp only [butlast_counter_succ, trace, current]
      by_cases e : x < b
      · rw [ite_eq_left e, ih (s + 1) (x + 1) (by omega)]
        push_cast
        by_cases f : (m : Int) ≤ b - (x + 1)
        · rw [ite_eq_left f, ite_eq_left (by omega)]; omega
        · rw [ite_eq_right f, ite_eq_right (by omega)]; grind
      · have : x = b := by omega
        subst this
        rw [ite_eq_right e, current_trace_second_phase (x + c) (s + 1) m x c (by omega) hc]
        push_cast
        rw [ite_eq_right (by omega)]
        grind

-- a follower: y increases by 1 whenever it does not exceed the value x of a counter with step 1, hence y is the
-- larger of its initial value and the final value of x, given that it starts at least at x
-- (from benchmark05_conjunctive)
theorem current_trace_catch_up (y0 : Int) (x0 : Int) (n : Nat) :
  x0 ≤ y0
    → current
      (trace
         y0
         (List.zip (butlast (counter 0 1 n)) (butlast (counter x0 1 n)))
         (fun y ⟨k, x⟩ => if y ≤ x then y + 1 else y))
      = (if x0 + integer n ≤ y0 then y0 else x0 + integer n) :=
  by
    intro h
    rw [integer_eq]
    suffices g : ∀ s y x, x ≤ y → current (trace y (List.zip (butlast (counter s 1 n)) (butlast (counter x 1 n)))
        (fun y ⟨k, x⟩ => if y ≤ x then y + 1 else y)) = (if x + (n : Int) ≤ y then y else x + n) from g 0 y0 x0 h
    induction n with
    | zero => intro s y x hxy; (simp [counter, butlast, trace, current]) <;> omega
    | succ m ih =>
      intro s y x hxy
      simp only [butlast_counter_succ, List.zip_cons_cons, trace, current]
      by_cases e : y ≤ x
      · rw [ite_eq_left e, ih (s + 1) (y + 1) (x + 1) (by omega)]; push_cast; split <;> split <;> omega
      · rw [ite_eq_right e, ih (s + 1) y (x + 1) (by omega)]; push_cast; split <;> split <;> omega

-- a flag, initially x0, that is set to c whenever D holds, is x0 at the end iff D never held, otherwise c
-- (from standard_compare_ground)
theorem current_trace_flag (x0 : Int) (c : Int) (n : Nat) (hs : List Int)
                                 (D : Int → Int → Prop) (hhs : length hs = n) :
  current
    (trace
       x0
       (List.zip (butlast (counter 0 1 n)) hs)
       (fun f ⟨k, h⟩ => if D k h then c else f))
    = (if invs
         (List.zip (butlast (counter 0 1 n)) hs)
         (fun ⟨k, h⟩ => ¬D k h) then
         x0
       else
         c) :=
  by
    induction (List.zip (butlast (counter 0 1 n)) hs) generalizing x0 with
    | nil => simp [trace, current, invs]
    | cons p ps ih =>
      obtain ⟨k, h⟩ := p
      simp only [trace, current, invs]
      rw [ih]
      by_cases d : D k h
      · simp only [d, ite_true, not_true, false_and, ite_false]
        -- once set to c, the flag stays c
        clear ih
        induction ps with
        | nil => simp [trace, current]
        | cons q qs ih2 => obtain ⟨k', h'⟩ := q; simp
      · simp [d]

-- a value multiplied by c in each iteration, a geometric sequence
-- (from underapprox_1-1, underapprox_1-2)
theorem current_trace_geometric (x0 : Int) (c : Int) (n : Nat) :
  current (trace x0 (butlast (counter 0 1 n)) (fun x k => c * x)) = x0 * pow c n :=
  by
    suffices h : ∀ (j d : Int), current (trace x0 (butlast (counter j d n)) (fun x k => c * x)) = x0 * pow c n from h 0 1
    induction n generalizing x0 with
    | zero => intro j d; simp [counter, butlast, trace, current, pow]
    | succ m ih => intro j d; simp only [butlast_counter_succ, trace, current, ih, pow]; grind

-- a value whose two increments are multiples of m keeps its remainder modulo m, a modular invariant
-- (from loopv1)
theorem current_trace_mod (x0 : Int) (n : Nat) (a : Int) (b : Int)
                                (m : Int) (hs : List Int) (C : Int → Prop)
                                (hhs : length hs = n) :
  0 < m ∧ a % m = 0 ∧ b % m = 0
    → current
      (trace
         x0
         (List.zip (butlast (counter 0 1 n)) hs)
         (fun x ⟨k, h⟩ => if C h then x + a else x + b))
      % m
      = x0 % m :=
  by
    intro ⟨hm, ha, hb⟩
    induction (List.zip (butlast (counter 0 1 n)) hs) generalizing x0 with
    | nil => simp [trace, current]
    | cons p ps ih =>
      obtain ⟨k, h⟩ := p
      simp only [trace, current]
      rw [ih]
      split <;> simp [Int.add_emod, ha, hb]

-- a sum that is set to c in the first iteration and adds G(i) in the others is c plus the sum of G over 1, ..., n - 1,
-- stated over the same iterations 0, ..., n - 1 with G(k) for 0 < k only, which the context of the map decides, rather
-- than over a new length n - 1; a conditional on n, which the simplifier decides by the value of integer(n)
-- (from brs1, brs1f, ms1, ms1f)
theorem current_trace_reset_add (x0 : Int) (n : Nat) (c : Int)
                                      (G : Int → Int) :
  current
    (trace
       x0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
       (fun x ⟨k, i⟩ => if i = 0 then c else G i + x))
    = (if n = zero then
         x0
       else
         c
           + sum
             (maps
                (butlast (counter 0 1 n))
                (fun k => if 0 < k then G k else 0))) :=
  by
    have later : ∀ (s x : Int) (m : Nat), 1 ≤ s → current (trace x (List.zip (butlast (counter s 1 m)) (butlast (counter s 1 m)))
        (fun x ⟨k, i⟩ => if i = 0 then c else G i + x)) = x + sum (maps (butlast (counter s 1 m)) G) := by
      intro s x m hs
      induction m generalizing s x with
      | zero => simp [counter, butlast, trace, current, maps, sum]
      | succ t ih =>
        simp only [butlast_counter_succ, List.zip_cons_cons, trace, current, maps, sum]
        rw [ite_eq_right (by omega), ih (s + 1) (G s + x) (by omega)]
        omega
    cases n with
    | zero => simp [counter, butlast, trace, current]
    | succ m =>
      have h := later 1 c m (by omega)
      have e : maps (butlast (counter 1 1 m)) (fun k => if 0 < k then G k else 0) = maps (butlast (counter 1 1 m)) (fun k => G k) :=
        maps_counter_congr 1 m _ _ (fun k hk => by simp [show 0 < k by omega])
      rw [sum_counter_succ]
      simp only [butlast_counter_succ, List.zip_cons_cons, trace, current, Int.zero_add] at h e ⊢
      simp only [ite_true, Nat.succ_ne_zero, ite_false]
      rw [h, e]
      simp

-- earlier

theorem earlier_counter (k : Nat) (i : Int) (c : Int) (n : Nat) :
  integer k < integer n → earlier k (butlast (counter i c n)) = i + integer k * c :=
  by
    intro h
    induction n generalizing i k with
    | zero => simp only [integer_eq] at h; omega
    | succ m ih =>
      cases k with
      | zero => simp [butlast_counter_succ, earlier, integer]
      | succ j =>
        have h' : integer j < integer m := by simp only [integer_eq] at h ⊢; omega
        simp [butlast_counter_succ, earlier, ih j (i + c) h', integer]; grind

theorem earlier_indexof {α : Type} [Inhabited α] (x : α) (xs : List α) :
  occurs x xs → earlier (indexof x xs) xs = x :=
  by
    induction xs with
    | nil => simp [occurs]
    | cons y ys ih =>
      intro h
      simp only [indexof]
      split
      · next h' => simp [earlier, ih h']
      · next h' => simp only [occurs] at h; rcases h with h | h; simp [earlier, h]; exact absurd h h'

theorem earlier_consts {α : Type} [Inhabited α] (k : Nat) (n : Nat)
                                                      (x : α) :
  integer k < integer n → earlier k (butlast (consts n x)) = x :=
  by
    intro h
    induction n generalizing k with
    | zero => simp only [integer_eq] at h; omega
    | succ m ih =>
      cases k with
      | zero => simp [consts, butlast, earlier]
      | succ j =>
        have h' : integer j < integer m := by simp only [integer_eq] at h ⊢; omega
        simp [consts, butlast, earlier, ih j h']

theorem earlier_selects {α β : Type} [Inhabited α] [Inhabited β] (j : Nat)
                                                                       (a : α → β)
                                                                       (keys : List α)
                                                                       (n : Nat)
                                                                       (hkeys : length keys = n) :
  integer j < integer n → earlier j (selects a keys) = a (earlier j keys) :=
  by
    intro h
    induction keys generalizing j n with
    | nil => rw [← hkeys] at h; simp only [integer_eq, List.length_nil] at h; omega
    | cons k ks ih =>
      cases j with
      | zero => simp [selects, maps, earlier]
      | succ i =>
        simp only [selects, maps, earlier]
        exact ih i ks.length rfl (by simp at hkeys; simp only [integer_eq] at h ⊢; omega)

theorem earlier_sums (j : Nat) (x : Int) (values : List Int) (n : Nat)
                           (hvalues : length values = n) :
  integer j < integer n → earlier j (butlast (sums x values)) = x + sum («prefix» j values) :=
  by
    intro h
    induction values generalizing j x n with
    | nil => rw [← hvalues] at h; simp only [integer_eq, List.length_nil] at h; omega
    | cons v vs ih =>
      have e : sums x (v :: vs) = .step x (sums (x + v) vs) := rfl
      rw [e]
      cases j with
      | zero => simp [butlast, earlier, «prefix», sum]
      | succ i =>
        simp only [butlast, earlier, «prefix», sum]
        rw [ih i (x + v) vs.length rfl (by simp at hvalues; simp only [integer_eq] at h ⊢; omega)]
        omega

theorem earlier_counts {α : Type} [Inhabited α] (j : Nat) (x : Int)
                                                      (e : α) (vs : List α)
                                                      (n : Nat)
                                                      (hvs : length vs = n) :
  integer j < integer n → earlier j (butlast (counts x e vs)) = x + count e («prefix» j vs) :=
  by
    intro h
    induction vs generalizing j x n with
    | nil => rw [← hvs] at h; simp only [integer_eq, List.length_nil] at h; omega
    | cons v vs ih =>
      have e' : counts x e (v :: vs) = .step x (counts (if v = e then x + 1 else x) e vs) := rfl
      rw [e']
      cases j with
      | zero => simp [butlast, earlier, «prefix», count]
      | succ i =>
        simp only [butlast, earlier, «prefix», count]
        rw [ih i _ vs.length rfl (by simp at hvs; simp only [integer_eq] at h ⊢; omega)]
        by_cases hv : v = e <;> simp [hv] <;> omega

theorem earlier_prefix {α : Type} [Inhabited α] (j : Nat) (k : Nat)
                                                      (xs : List α) :
  integer j < integer k → earlier j («prefix» k xs) = earlier j xs :=
  by
    intro h
    induction xs generalizing j k with
    | nil => cases k <;> simp [«prefix», earlier]
    | cons x xs ih =>
      cases k with
      | zero => simp only [integer_eq] at h; omega
      | succ m =>
        cases j with
        | zero => simp [«prefix», earlier]
        | succ i => simp only [«prefix», earlier]; exact ih i m (by simp only [integer_eq] at h ⊢; omega)

-- agreeing sequences are equal at each position in the range; the atom is the left-hand side
-- (from standard_compare_ground)
theorem earlier_agree_prefix (n : Nat) (j : Nat) (xs : List Int)
                                   (ys : List Int) :
  agree_prefix n xs ys ∧ integer j < integer n
    → (earlier j xs = earlier j ys ↔ True) :=
  by
    intro ⟨h, hj⟩
    simp only [iff_true]
    simp only [integer_eq] at hj
    induction n with
    | zero => omega
    | succ m ih =>
      simp only [agree_prefix] at h
      by_cases e : j = m
      · subst e; exact h.2
      · exact ih h.1 (by omega)

-- which is instantiated at the positions j in that range
-- (from standard_find_ground-1)
theorem earlier_not_occurs_prefix (n : Nat) (j : Nat) (e : Int)
                                        (xs : List Int) (hxs : length xs = n) :
  ¬occurs e («prefix» n xs) ∧ integer j < integer n → (earlier j xs = e ↔ False) :=
  by
    intro ⟨h1, h2⟩
    rw [not_occurs_prefix_forall n xs e hxs] at h1
    simp only [integer_eq] at h2
    exact iff_false_intro (h1 j (by omega))

-- the same for reads of an array, at the positions k of the counter
-- (from lsearch)
theorem select_not_occurs_selects (a : Int → Int) (x : Int) (i : Int)
                                        (n : Nat) (k : Int) :
  ¬occurs x (selects a (butlast (counter i 1 n))) ∧ i ≤ k ∧ k < i + integer n
    → (a k = x ↔ False) :=
  by
    intro ⟨h, h1, h2⟩
    simp only [iff_false]
    intro e
    apply h
    rw [integer_eq] at h2
    clear h
    simp only [selects]
    induction n generalizing i with
    | zero => (simp at h2) <;> omega
    | succ m ih =>
      simp only [butlast_counter_succ, maps, occurs]
      by_cases hk : k = i
      · left; rw [← hk, e]
      · right; exact ih (i + 1) (by omega) (by push_cast at h2; omega)

theorem select_not_occurs_selects_beyond (n : Nat) (j : Int) (x : Int)
                                               (a : Int → Int) :
  ¬occurs x (selects a (butlast (counter 0 1 n))) ∧ a j = x ∧ 0 ≤ j
    → integer n ≤ j :=
  by
    intro ⟨h, e, hj⟩
    rcases Int.lt_or_le j (integer n) with hlt | hle
    · exact ((select_not_occurs_selects a x 0 n j ⟨h, hj, by omega⟩).mp e).elim
    · exact hle

theorem select_store_other {α β : Type} [Inhabited α] [Inhabited β] (a : α → β)
                                                                          (i : α)
                                                                          (v : β)
                                                                          (j : α) :
  j ≠ i → (fun j => if j = i then v else a j) j = a j :=
  by intro h; simp [h]

-- prefix

theorem prefix_counter (k : Nat) (i : Int) (c : Int) (n : Nat) :
  integer k ≤ integer n → «prefix» k (butlast (counter i c n)) = butlast (counter i c k) :=
  by
    intro h
    induction n generalizing i k with
    | zero => cases k with
      | zero => rfl
      | succ j => simp only [integer_eq] at h; omega
    | succ m ih => cases k with
      | zero => rfl
      | succ j =>
        simp only [butlast_counter_succ, «prefix»]
        rw [ih j (i + c) (by simp only [integer_eq] at h ⊢; omega)]

theorem prefix_maps_counter (k : Nat) (i : Int) (c : Int) (n : Nat)
                                  (ys : List Int) (F : Int → Int)
                                  (hys : length ys = n) :
  integer k ≤ integer n
    → «prefix»
      k
      (maps (List.zip (butlast (counter i c n)) ys) (fun ⟨v, y⟩ => F v))
      = maps (butlast (counter i c k)) (fun v => F v) :=
  by
    intro h
    induction n generalizing i k ys with
    | zero => cases k with
      | zero => rfl
      | succ j => simp only [integer_eq] at h; omega
    | succ m ih =>
      cases ys with
      | nil => simp at hys
      | cons y ys => cases k with
        | zero => rfl
        | succ j =>
          simp only [butlast_counter_succ, List.zip_cons_cons, maps, «prefix»]
          rw [ih j (i + c) ys (by simpa using hys) (by simp only [integer_eq] at h ⊢; omega)]

theorem prefix_consts {α : Type} [Inhabited α] (k : Nat) (n : Nat)
                                                     (x : α) :
  integer k ≤ integer n → «prefix» k (butlast (consts n x)) = butlast (consts k x) :=
  by
    intro h
    induction n generalizing k with
    | zero => cases k with
      | zero => rfl
      | succ j => simp only [integer_eq] at h; omega
    | succ m ih => cases k with
      | zero => rfl
      | succ j =>
        simp only [consts, butlast, «prefix»]
        rw [ih j (by simp only [integer_eq] at h ⊢; omega)]

theorem prefix_selects {α β : Type} [Inhabited α] [Inhabited β] (k : Nat)
                                                                      (a : α → β)
                                                                      (keys : List α)
                                                                      (n : Nat)
                                                                      (hkeys : length keys = n) :
  «prefix» k (selects a keys) = selects a («prefix» k keys) :=
  by
    clear hkeys n
    induction keys generalizing k with
    | nil => cases k <;> simp [selects, maps, «prefix»]
    | cons x xs ih => cases k <;> simp [selects, maps, «prefix»] at * <;> exact ih _

theorem prefix_stores {α β : Type} [Inhabited α] [Inhabited β] (k : Nat)
                                                                     (a : α → β)
                                                                     (keys : List α)
                                                                     (values : List β)
                                                                     (n : Nat)
                                                                     (hkeys : length keys = n)
                                                                     (hvalues : length values = n) :
  «prefix» k (butlast (stores a keys values))
    = butlast (stores a («prefix» k keys) («prefix» k values)) :=
  by simp only [stores]; rw [prefix_butlast_trace, prefix_zip]

theorem prefix_sums (k : Nat) (x : Int) (values : List Int) (n : Nat)
                          (hvalues : length values = n) :
  «prefix» k (butlast (sums x values)) = butlast (sums x («prefix» k values)) :=
  by simp only [sums]; exact prefix_butlast_trace k x values _

theorem prefix_maxs (k : Nat) (x : Int) (values : List Int) (n : Nat)
                          (hvalues : length values = n) :
  «prefix» k (butlast (maxs x values)) = butlast (maxs x («prefix» k values)) :=
  by simp only [maxs]; exact prefix_butlast_trace k x values _

theorem prefix_mins (k : Nat) (x : Int) (values : List Int) (n : Nat)
                          (hvalues : length values = n) :
  «prefix» k (butlast (mins x values)) = butlast (mins x («prefix» k values)) :=
  by simp only [mins]; exact prefix_butlast_trace k x values _

theorem prefix_counts {α : Type} [Inhabited α] (k : Nat) (x : Int) (e : α)
                                                     (vs : List α) (n : Nat)
                                                     (hvs : length vs = n) :
  «prefix» k (butlast (counts x e vs)) = butlast (counts x e («prefix» k vs)) :=
  by simp only [counts]; exact prefix_butlast_trace k x vs _

theorem prefix_zero {α : Type} [Inhabited α] (xs : List α) :
  «prefix» zero xs = nil :=
  by cases xs <;> rfl

theorem prefix_prefix {α : Type} [Inhabited α] (j : Nat) (k : Nat)
                                                     (xs : List α) :
  integer j ≤ integer k → «prefix» j («prefix» k xs) = «prefix» j xs :=
  by
    intro h
    induction xs generalizing j k with
    | nil => cases k <;> cases j <;> rfl
    | cons x xs ih =>
      cases k with
      | zero => cases j with
        | zero => rfl
        | succ i => simp only [integer_eq] at h; omega
      | succ m => cases j with
        | zero => rfl
        | succ i =>
          simp only [«prefix»]
          rw [ih i m (by simp only [integer_eq] at h ⊢; omega)]

-- occurs

-- a value read at one of the keys occurs among the values read at them
theorem occurs_selects {α β : Type} [Inhabited α] [Inhabited β] (k : α)
                                                                      (a : α → β)
                                                                      (keys : List α)
                                                                      (n : Nat)
                                                                      (hkeys : length keys = n) :
  occurs k keys → occurs (a k) (selects a keys) :=
  by
    clear hkeys n
    induction keys with
    | nil => simp [occurs]
    | cons y ys ih => simp only [occurs, selects, maps] at *; intro h; rcases h with h | h; exact Or.inl (by rw [h]); exact Or.inr (ih h)

-- a value at an index occurs in the sequence, e.g. a stored value, which current(stores(a, keys, values))[k] reads
-- as earlier(indexof(k, keys), values) if k occurs among the keys; the indices of earlier are valid by construction
theorem occurs_earlier {α : Type} [Inhabited α] (j : Nat) (xs : List α) (n : Nat) (hxs : length xs = n) :
  integer j < integer n → occurs (earlier j xs) xs :=
  by
    intro h
    induction xs generalizing j n with
    | nil => rw [← hxs] at h; simp only [integer_eq, List.length_nil] at h; omega
    | cons x xs ih =>
      cases j with
      | zero => simp [earlier, occurs]
      | succ i =>
        simp only [earlier, occurs]
        exact Or.inr (ih i xs.length rfl (by simp at hxs; simp only [integer_eq] at h ⊢; omega))

theorem occurs_counter_up (j : Int) (i : Int) (n : Nat) :
  occurs j (butlast (counter i 1 n)) ↔ i ≤ j ∧ j < i + integer n :=
  by
    induction n generalizing i with
    | zero => (simp [counter, butlast, occurs, integer]) <;> omega
    | succ m ih => simp only [butlast_counter_succ, occurs, ih, integer_eq]; omega

theorem occurs_counter_down (j : Int) (i : Int) (n : Nat) :
  occurs j (butlast (counter i (-1) n)) ↔ i - integer n < j ∧ j ≤ i :=
  by
    induction n generalizing i with
    | zero => (simp [counter, butlast, occurs, integer]) <;> omega
    | succ m ih => simp only [butlast_counter_succ, occurs, ih, integer_eq]; omega

theorem occurs_consts {α : Type} [Inhabited α] (x : α) (n : Nat) (y : α) :
  occurs x (butlast (consts n y)) ↔ n ≠ zero ∧ x = y :=
  by
    induction n with
    | zero => simp [consts, butlast, occurs]
    | succ m ih => simp only [consts, butlast, occurs]; rw [ih]; grind

theorem occurs_prefix {α : Type} [Inhabited α] (x : α) (k : Nat) (xs : List α) :
  occurs x («prefix» k xs) → occurs x xs :=
  by
    induction xs generalizing k with
    | nil => cases k <;> simp [«prefix», occurs]
    | cons y ys ih =>
      cases k with
      | zero => simp [«prefix», occurs]
      | succ m => simp only [«prefix», occurs]; intro h; rcases h with h | h; exact Or.inl h; exact Or.inr (ih m h)

-- j occurs among the values of a counter with a positive step d iff it is in the range and a multiple of d from the
-- initial value (teq.dfy has this for the step 1)
-- (from array_monotonic)
theorem occurs_counter_step (i : Int) (d : Int) (n : Nat) (j : Int) :
  0 < d
    → (occurs j (butlast (counter i d n))
         ↔ i ≤ j ∧ j < i + integer n * d ∧ (j - i) % d = 0) :=
  by
    intro hd
    induction n generalizing i with
    | zero => simp [counter, butlast, occurs, integer]; omega
    | succ m ih =>
      simp only [butlast_counter_succ, occurs, ih, integer_eq]
      push_cast
      constructor
      · rintro (h | ⟨h1, h2, h3⟩)
        · subst h; refine ⟨Int.le_refl _, ?_, by simp⟩; have := Int.mul_le_mul_of_nonneg_right (show (0:Int) ≤ m by omega) (Int.le_of_lt hd); grind
        · refine ⟨by omega, by grind, ?_⟩
          have : j - i = (j - (i + d)) + d := by omega
          rw [this, Int.add_emod_right]; exact h3
      · rintro ⟨h1, h2, h3⟩
        by_cases e : i = j
        · exact Or.inl e
        · right
          obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero h3
          have hq1 : 1 ≤ q := by
            rcases Int.lt_or_le 0 q with h | h
            · omega
            · have := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hd); grind
          have hdq := Int.mul_le_mul_of_nonneg_left hq1 (Int.le_of_lt hd)
          rw [Int.mul_one] at hdq
          refine ⟨by omega, by grind, ?_⟩
          have : j - (i + d) = d * (q - 1) := by grind
          rw [this]; simp

-- indexof

theorem indexof_counter_up (j : Int) (i : Int) (n : Nat) :
  i ≤ j ∧ j < i + integer n
    → indexof j (butlast (counter i 1 n)) = natural (j - i) :=
  by
    intro ⟨h1, h2⟩
    rw [integer_eq] at h2
    induction n generalizing i with
    | zero => (simp at h2) <;> omega
    | succ m ih =>
      rw [butlast_counter_succ, indexof]
      have hocc : occurs j (butlast (counter (i + 1) 1 m)) ↔ i + 1 ≤ j := by
        rw [occurs_counter_up, integer_eq]; push_cast at h2; omega
      by_cases e : i + 1 ≤ j
      · rw [ite_eq_left (hocc.mpr e), ih (i + 1) e (by push_cast at h2; omega), natural_eq, natural_eq]
        show (j - (i + 1)).toNat + 1 = (j - i).toNat
        omega
      · rw [ite_eq_right (fun h => e (hocc.mp h)), natural_eq]
        show (0 : Nat) = (j - i).toNat
        omega

theorem indexof_counter_down (j : Int) (i : Int) (n : Nat) :
  i - integer n < j ∧ j ≤ i
    → indexof j (butlast (counter i (-1) n)) = natural (i - j) :=
  by
    intro ⟨h1, h2⟩
    rw [integer_eq] at h1
    induction n generalizing i with
    | zero => (simp at h1) <;> omega
    | succ m ih =>
      rw [butlast_counter_succ, indexof]
      have hocc : occurs j (butlast (counter (i + -1) (-1) m)) ↔ j ≤ i + -1 := by
        rw [occurs_counter_down, integer_eq]; push_cast at h1; omega
      by_cases e : j ≤ i + -1
      · rw [ite_eq_left (hocc.mpr e), ih (i + -1) (by push_cast at h1; omega) e, natural_eq, natural_eq]
        show (i + -1 - j).toNat + 1 = (i - j).toNat
        omega
      · rw [ite_eq_right (fun h => e (hocc.mp h)), natural_eq]
        show (0 : Nat) = (i - j).toNat
        omega

theorem indexof_counter_step (j : Int) (i : Int) (d : Int) (n : Nat) :
  0 < d ∧ i ≤ j ∧ j < i + integer n * d ∧ (j - i) % d = 0
    → indexof j (butlast (counter i d n)) = natural ((j - i) / d) :=
  by
    intro ⟨hd, h1, h2, h3⟩
    rw [integer_eq] at h2
    induction n generalizing i with
    | zero => (simp at h2) <;> omega
    | succ m ih =>
      push_cast at h2
      rw [Int.add_mul, Int.one_mul] at h2
      have h3' : (j - (i + d)) % d = 0 := by
        have : j - (i + d) = (j - i) + (-1) * d := by omega
        rw [this, Int.add_mul_emod_self_right]; exact h3
      rw [butlast_counter_succ, indexof]
      have hocc : occurs j (butlast (counter (i + d) d m)) ↔ i + d ≤ j := by
        rw [occurs_counter_step (i + d) d m j hd, integer_eq]
        constructor
        · intro ⟨a, _, _⟩; exact a
        · intro a; exact ⟨a, by omega, h3'⟩
      by_cases e : i + d ≤ j
      · rw [ite_eq_left (hocc.mpr e), ih (i + d) e (by omega) h3', natural_eq, natural_eq]
        have hq : (j - i) / d = (j - (i + d)) / d + 1 := by
          have : j - i = (j - (i + d)) + 1 * d := by omega
          rw [this, Int.add_mul_ediv_right _ _ (by omega)]
        have : 0 ≤ (j - (i + d)) / d := Int.ediv_nonneg (by omega) (by omega)
        omega
      · rw [ite_eq_right (fun h => e (hocc.mp h)), natural_eq]
        have : (j - i) / d = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
        show (0 : Nat) = ((j - i) / d).toNat
        omega

-- distincts

theorem distincts_counter (i : Int) (c : Int) (n : Nat) :
  c ≠ 0 → distincts (butlast (counter i c n)) :=
  by
    intro hc
    induction n generalizing i with
    | zero => simp [counter, butlast, distincts]
    | succ m ih =>
      simp only [butlast_counter_succ, distincts]
      refine ⟨?_, ih (i + c)⟩
      intro h
      -- the values after i differ from it, since they are i + (k + 1) * c
      have key : ∀ (m : Nat) (j : Int), occurs i (butlast (counter j c m)) → ∃ k : Nat, k < m ∧ i = j + k * c := by
        intro m
        induction m with
        | zero => intro j h; simp [counter, butlast, occurs] at h
        | succ m ih2 =>
          intro j h
          simp only [butlast_counter_succ, occurs] at h
          rcases h with h | h
          · exact ⟨0, by omega, by simp [h]⟩
          · obtain ⟨k, hk, e⟩ := ih2 (j + c) h
            exact ⟨k + 1, by omega, by rw [e]; push_cast; grind⟩
      obtain ⟨k, _, e⟩ := key m (i + c) h
      have : ((k : Int) + 1) * c = 0 := by grind
      rcases Int.mul_eq_zero.mp this with h' | h' <;> omega

theorem distincts_prefix {α : Type} [Inhabited α] (k : Nat) (xs : List α) :
  distincts xs → distincts («prefix» k xs) :=
  by
    induction xs generalizing k with
    | nil => cases k <;> simp [«prefix», distincts]
    | cons y ys ih =>
      cases k with
      | zero => simp [«prefix», distincts]
      | succ m =>
        simp only [«prefix», distincts]
        intro ⟨h1, h2⟩
        exact ⟨fun h => h1 (occurs_prefix y m ys h), ih m h2⟩

-- selects

theorem selects_stores {α β : Type} [Inhabited α] [Inhabited β] (a : α → β)
                                                                      (keys : List α)
                                                                      (values : List β)
                                                                      (n : Nat)
                                                                      (hkeys : length keys = n)
                                                                      (hvalues : length values = n) :
  distincts keys → selects (current (stores a keys values)) keys = values :=
  by
    intro hd
    induction keys generalizing a values n with
    | nil => cases values with
      | nil => rfl
      | cons v vs => simp at hkeys hvalues; omega
    | cons k ks ih =>
      cases values with
      | nil => simp at hkeys hvalues; omega
      | cons v vs =>
        simp only [distincts] at hd
        have e : stores a (k :: ks) (v :: vs) = .step a (stores (fun j => if j = k then v else a j) ks vs) := rfl
        rw [e]
        simp only [current, selects, maps]
        rw [current_stores_not_occurs _ ks vs k hd.1]
        simp only [ite_true]
        congr 1
        exact ih (a := fun j => if j = k then v else a j) (values := vs) (n := ks.length) rfl (by simp at hkeys hvalues; omega) hd.2

theorem selects_shifts (a : Int → Int) (n : Nat) (i : Int) (d : Int) :
  0 ≤ d
    → selects
      (current (shifts a (butlast (counter i 1 n)) d))
      (butlast (counter i 1 n))
      = selects a (butlast (counter (i + d) 1 n)) :=
  by
    intro hd
    simp only [selects]
    rw [maps_counter_offset i d n (fun k => a k)]
    apply maps_counter_congr
    intro k hk
    simp only [shifts]
    rw [shifts_general d hd a k n i a (fun _ _ => rfl), ite_eq_left hk]

-- the elements of stores at the positions of a counter, read at the positions of the same counter, are the stored
-- values; both counters are patterns, since they are different trace variables in programs
-- (from conda, condaf, ss1, ss1f)
theorem selects_stores_counter (a : Int → Int) (i : Int) (c : Int)
                                     (n : Nat) (vs : List Int)
                                     (hvs : length vs = n) :
  c ≠ 0
    → selects
      (current (stores a (butlast (counter i c n)) vs))
      (butlast (counter i c n))
      = vs :=
  by
    intro hc
    exact selects_stores a _ vs n (length_butlast_counter i c n) hvs (distincts_counter i c n hc)

-- sums

-- the prefix sums of n copies of c, from x, are the counter from x by c: the counter of an inner loop, whose trace is
-- folded into sums over its dependency before that is known to be a counter (see examples/dafny/sorting/nested_sum.dfy)
theorem sums_consts (x : Int) (n : Nat) (c : Int) :
  sums x (butlast (consts n c)) = counter x c n :=
  by
    induction n generalizing x with
    | zero => rfl
    | succ m ih =>
      rw [show butlast (consts (m + 1) c) = c :: butlast (consts m c) from rfl,
          show sums x (c :: butlast (consts m c)) = .step x (sums (x + c) (butlast (consts m c))) from rfl, ih (x + c)]
      rfl

-- array selects

theorem current_stores {α β : Type} [Inhabited α] [Inhabited β] (k : α)
                                                                      (a : α → β)
                                                                      (keys : List α)
                                                                      (values : List β)
                                                                      (n : Nat)
                                                                      (hkeys : length keys = n)
                                                                      (hvalues : length values = n) :
  current (stores a keys values) k
    = (if occurs k keys then earlier (indexof k keys) values else a k) :=
  by
    induction keys generalizing a values n with
    | nil => simp [stores, trace, current, occurs]
    | cons k' ks ih =>
      cases values with
      | nil => simp at hkeys hvalues; omega
      | cons v vs =>
        have e : stores a (k' :: ks) (v :: vs) = .step a (stores (fun j => if j = k' then v else a j) ks vs) := rfl
        rw [e]
        simp only [current]
        rw [ih (a := fun j => if j = k' then v else a j) (values := vs) (n := ks.length) rfl (by simp at hkeys hvalues; omega)]
        simp only [occurs, indexof]
        by_cases ho : occurs k ks
        · simp [ho, earlier]
        · by_cases hk : k' = k
          · subst hk; simp [ho, earlier]
          · simp [ho, hk, Ne.symm hk]

-- an earlier state reads the value stored last at k among the keys stored so far, the initial value otherwise
-- (indexof is the *last* occurrence, hence indexof(k, prefix(j, keys)) <= indexof(k, keys) but not equal)
theorem earlier_stores {α β : Type} [Inhabited α] [Inhabited β] (k : α)
                                                                      (j : Nat)
                                                                      (a : α → β)
                                                                      (keys : List α)
                                                                      (values : List β)
                                                                      (n : Nat)
                                                                      (hkeys : length keys = n)
                                                                      (hvalues : length values = n) :
  integer j < integer n → earlier j (butlast (stores a keys values)) k
    = (if occurs k («prefix» j keys) then
         earlier (indexof k («prefix» j keys)) values
       else
         a k) :=
  by
    intro h
    simp only [integer_eq] at h
    have hlen : (List.zip keys values).length = n := length_zip_eq keys values n hkeys hvalues
    rw [stores, earlier_butlast_trace j a (List.zip keys values) _ (by omega), prefix_zip, ← stores,
        current_stores k a («prefix» j keys) («prefix» j values) j (length_prefix j keys (by omega))
          (length_prefix j values (by omega))]
    by_cases ho : occurs k («prefix» j keys)
    · simp only [ho, ite_true]
      have hi := indexof_lt_length k _ ho
      rw [length_prefix j keys (by omega)] at hi
      rw [earlier_prefix _ j values (by simp only [integer_eq]; omega)]
    · simp only [ho, ite_false]

theorem current_shifts (a : Int → Int) (n : Nat) (i : Int) (d : Int)
                             (k : Int) :
  0 ≤ d
    → current (shifts a (butlast (counter i 1 n)) d) k
      = (if i ≤ k ∧ k < i + integer n then a (k + d) else a k) :=
  by
    intro hd
    simp only [shifts]
    rw [shifts_general d hd a k n i a (fun _ _ => rfl), integer_eq]

-- stores at the positions of a counter, guarded by C, keep the other positions; a read at j
-- (from copysome1-1, copysome1-2)
theorem current_trace_conditional_store (a0 : Int → Int) (n : Nat)
                                              (j : Int) (C : Int → Prop)
                                              (V : Int → Int) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
       (fun a ⟨k, i⟩ => if C i then fun j => if j = i then V i else a j else a))
    j
    = (if 0 ≤ j ∧ j < integer n ∧ C j then V j else a0 j) :=
  by
    rw [integer_eq]
    suffices g : ∀ (s : Int) (a : Int → Int), current (trace a (List.zip (butlast (counter s 1 n)) (butlast (counter s 1 n)))
        (fun a ⟨k, i⟩ => if C i then fun j => if j = i then V i else a j else a)) j
        = (if s ≤ j ∧ j < s + n ∧ C j then V j else a j) by simpa using g 0 a0
    induction n with
    | zero => intro s a; simp [counter, butlast, trace, current]; omega
    | succ m ih =>
      intro s a
      simp only [butlast_counter_succ, List.zip_cons_cons, trace, current]
      rw [ih (s + 1)]
      push_cast
      by_cases e : j = s
      · subst e; by_cases hC : C j <;> simp [hC] <;> omega
      · by_cases hC : C s <;> simp [hC, e] <;> (repeat' split) <;> grind

-- the same, with the guard and the value on the values of three further dependencies at the iteration of j
-- (from array_mul_init)
theorem current_trace_conditional_store_deps (a0 : Int → Int) (n : Nat)
                                                   (j : Int) (hs : List Int)
                                                   (cs : List Int)
                                                   (vs : List Int)
                                                   (C : Int → Int → Int → Prop)
                                                   (V : Int → Int → Int → Int)
                                                   (hhs : length hs = n)
                                                   (hcs : length cs = n)
                                                   (hvs : length vs = n) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) (List.zip hs (List.zip cs vs)))
       (fun a ⟨k, h, c, v⟩ =>
          if C h c v then fun j => if j = k then V h c v else a j else a))
    j
    = (if 0 ≤ j
         ∧ j < integer n
         ∧ C
           (earlier (natural j) hs)
           (earlier (natural j) cs)
           (earlier (natural j) vs) then
         V
           (earlier (natural j) hs)
           (earlier (natural j) cs)
           (earlier (natural j) vs)
       else
         a0 j) :=
  by
    rw [integer_eq]
    -- the loop from s on, where position s is written in the first iteration and the later ones from s + 1 on
    have gen : ∀ (m : Nat) (s : Int) (b : Int → Int) (hs cs vs : List Int),
        hs.length = m → cs.length = m → vs.length = m →
        current (trace b (List.zip (butlast (counter s 1 m)) (List.zip hs (List.zip cs vs)))
          (fun a ⟨k, h, c, v⟩ => if C h c v then fun j => if j = k then V h c v else a j else a)) j
        = (if s ≤ j ∧ j < s + m
              ∧ C (earlier (natural (j - s)) hs) (earlier (natural (j - s)) cs) (earlier (natural (j - s)) vs)
           then V (earlier (natural (j - s)) hs) (earlier (natural (j - s)) cs) (earlier (natural (j - s)) vs)
           else b j) := by
      intro m
      induction m with
      | zero =>
        intro s b hs cs vs h1 h2 h3
        cases hs with
        | nil =>
          simp only [counter, butlast, List.zip_nil_left, trace, current]
          exact (ite_eq_right (by intro ⟨_, h', _⟩; simp at h'; omega)).symm
        | cons _ _ => simp at h1
      | succ t ih =>
        intro s b hs cs vs h1 h2 h3
        cases hs with
        | nil => simp at h1
        | cons h hs =>
          cases cs with
          | nil => simp at h2
          | cons c cs =>
            cases vs with
            | nil => simp at h3
            | cons v vs =>
              rw [butlast_counter_succ, List.zip_cons_cons, List.zip_cons_cons, List.zip_cons_cons]
              simp only [trace, current]
              rw [ih (s + 1) _ hs cs vs (by simp at h1; omega) (by simp at h2; omega) (by simp at h3; omega)]
              push_cast
              rcases Int.lt_trichotomy j s with hj | hj | hj
              · -- before the first position: nothing is written
                have hn : ¬(s + 1 ≤ j) := by omega
                have hn' : ¬(s ≤ j) := by omega
                simp only [hn, hn', false_and, ite_false]
                by_cases hC : C h c v <;> simp [hC, show j ≠ s by omega]
              · -- the first position
                subst hj
                have hn : ¬(j + 1 ≤ j) := by omega
                simp only [hn, false_and, ite_false, Int.sub_self, natural_zero, earlier]
                have hb : j ≤ j ∧ j < j + ((t : Int) + 1) := ⟨by omega, by omega⟩
                by_cases hC : C h c v <;> simp [hC, hb]
              · -- later positions: the first iteration does not write them
                have hn : natural (j - s) = succ (natural (j - (s + 1))) := by
                  rw [natural, ite_eq_right (by omega : ¬(j - s ≤ 0))]
                  congr 2
                  omega
                simp only [hn, earlier]
                have hb : (fun j' => if j' = s then V h c v else b j') j = b j := by simp [show j ≠ s by omega]
                by_cases hC : C h c v <;> simp only [hC, ite_true, ite_false, hb]
                  <;> by_cases hC2 : C (earlier (natural (j - (s + 1))) hs) (earlier (natural (j - (s + 1))) cs)
                        (earlier (natural (j - (s + 1))) vs)
                  <;> simp only [hC2, and_true, and_false, ite_false]
                  <;> split <;> split <;> first | rfl | omega
    have := gen n 0 a0 hs cs vs hhs hcs hvs
    simpa using this

-- the same, at distinct positions ps, which are kept as matched, read by occurs and indexof
-- (from array_monotonic)
theorem current_trace_conditional_store_distinct (a0 : Int → Int)
                                                       (n : Nat) (j : Int)
                                                       (ps : List Int)
                                                       (cs : List Int)
                                                       (C : Int → Int → Prop)
                                                       (V : Int → Int → Int)
                                                       (hps : length ps = n)
                                                       (hcs : length cs = n) :
  distincts ps
    → current
      (trace
         a0
         (List.zip (butlast (counter 0 1 n)) (List.zip ps cs))
         (fun a ⟨k, p, c⟩ =>
            if C p c then fun j => if j = p then V p c else a j else a))
      j
      = (if occurs j ps ∧ C j (earlier (indexof j ps) cs) then
           V j (earlier (indexof j ps) cs)
         else
           a0 j) :=
  by
    intro hd
    -- the counter only gives the length: the result for any list of keys of the right length
    have gen : ∀ (ps cs ks : List Int) (b : Int → Int), ps.length = cs.length → ks.length = ps.length → distincts ps →
        current (trace b (List.zip ks (List.zip ps cs))
          (fun a ⟨k, p, c⟩ => if C p c then fun j => if j = p then V p c else a j else a)) j
        = (if occurs j ps ∧ C j (earlier (indexof j ps) cs) then V j (earlier (indexof j ps) cs) else b j) := by
      intro ps
      induction ps with
      | nil =>
        intro cs ks b h1 h2 hd
        cases ks with
        | nil => simp [trace, current, occurs]
        | cons _ _ => simp at h2
      | cons p ps ih =>
        intro cs ks b h1 h2 hd
        cases cs with
        | nil => simp at h1
        | cons c cs =>
          cases ks with
          | nil => simp at h2
          | cons k ks =>
            simp only [distincts] at hd
            rw [List.zip_cons_cons, List.zip_cons_cons]
            simp only [trace, current]
            rw [ih cs ks _ (by simp at h1; omega) (by simp at h2; omega) hd.2]
            simp only [occurs, indexof]
            by_cases ho : occurs j ps
            · have hpj : p ≠ j := fun e => hd.1 (e ▸ ho)
              simp only [ho, ite_true, or_true, true_and, earlier]
              by_cases hC : C p c <;> simp [hC, Ne.symm hpj]
            · simp only [ho, ite_false, or_false, false_and, earlier]
              by_cases hpj : p = j
              · subst hpj; by_cases hC : C p c <;> simp [hC]
              · by_cases hC : C p c <;> simp [hC, hpj, Ne.symm hpj]
    exact gen ps cs _ a0 (by rw [hps, hcs]) (by rw [length_butlast_counter, hps]) hd

-- a clamp of each element to b, where the guard reads the initial element, since each position is written in its own
-- iteration only; a generic guard C(a[k], k) is no pattern, and C(a, k) would read other positions
-- (from condn, condnf)
theorem current_trace_cap (a0 : Int → Int) (n : Nat) (j : Int) (b : Int)
                                (hs : List Int) (hhs : length hs = n) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) hs)
       (fun a ⟨k, h⟩ =>
          if a k < b then a else fun j => if j = k then b else a j))
    j
    = (if 0 ≤ j ∧ j < integer n ∧ b ≤ a0 j then b else a0 j) :=
  by
    rw [integer_eq]
    -- from position s on, where the positions from s on still hold their initial values
    have gen : ∀ (m : Nat) (s : Int) (a : Int → Int) (hs : List Int), hs.length = m → (∀ x, s ≤ x → a x = a0 x) →
        current (trace a (List.zip (butlast (counter s 1 m)) hs)
          (fun a ⟨k, h⟩ => if a k < b then a else fun j => if j = k then b else a j)) j
        = (if s ≤ j ∧ j < s + m ∧ b ≤ a0 j then b else a j) := by
      intro m
      induction m with
      | zero =>
        intro s a hs h1 ha
        cases hs with
        | nil =>
          simp only [counter, butlast, List.zip_nil_left, trace, current]
          exact (ite_eq_right (by intro ⟨_, h', _⟩; simp at h'; omega)).symm
        | cons _ _ => simp at h1
      | succ t ih =>
        intro s a hs h1 ha
        cases hs with
        | nil => simp at h1
        | cons h hs =>
          rw [butlast_counter_succ, List.zip_cons_cons]
          simp only [trace, current]
          rw [ih (s + 1) _ hs (by simp at h1; omega)
            (by intro x hx; by_cases hc : a s < b <;> simp [hc, show x ≠ s by omega, ha x (by omega)])]
          push_cast
          rw [ha s (by omega)]
          rcases Int.lt_trichotomy j s with hj | hj | hj
          · have hn : ¬(s + 1 ≤ j) := by omega
            have hn' : ¬(s ≤ j) := by omega
            simp only [hn, hn', false_and, ite_false]
            by_cases hc : a0 s < b <;> simp [hc, show j ≠ s by omega]
          · subst hj
            have hn : ¬(j + 1 ≤ j) := by omega
            simp only [hn, false_and, ite_false]
            have hb : j ≤ j ∧ j < j + ((t : Int) + 1) := ⟨by omega, by omega⟩
            by_cases hc : a0 j < b
            · simp [hc, hb, show ¬(b ≤ a0 j) by omega]
            · simp [hc, hb, show b ≤ a0 j by omega]
          · have hb : (fun j' => if j' = s then b else a j') j = a j := by simp [show j ≠ s by omega]
            by_cases hc : a0 s < b <;> simp only [hc, ite_true, ite_false, hb]
              <;> split <;> split <;> first | rfl | omega
    have := gen n 0 a0 hs hhs (fun _ _ => rfl)
    simpa using this

-- an array filled by a recurrence at the positions 1, ..., n, each element from its predecessor plus G of the position
-- of the predecessor, is the initial element plus the sum of G over the positions before
-- (from eqn1, eqn1f, nsqm, nsqmf, pcomp, pcompf, sqm)
theorem current_trace_prefix_sums (b0 : Int → Int) (n : Nat) (j : Int)
                                        (G : Int → Int) :
  current
    (trace
       b0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 1 1 n)))
       (fun b ⟨k, i⟩ => fun j => if j = i then G k + b k else b j))
    j
    = (if 0 ≤ j ∧ j ≤ integer n then
         b0 0 + sum (maps (butlast (counter 0 1 (natural j))) (fun k => G k))
       else
         b0 j) :=
  by
    rw [integer_eq, natural_eq]
    suffices g : ∀ (s : Int) (b : Int → Int), current (trace b (List.zip (butlast (counter s 1 n)) (butlast (counter (s + 1) 1 n)))
        (fun b ⟨k, i⟩ => fun j => if j = i then G k + b k else b j)) j
        = (if s ≤ j ∧ j ≤ s + n then b s + sum (maps (butlast (counter s 1 (j - s).toNat)) (fun k => G k)) else b j) by
      simpa using g 0 b0
    induction n with
    | zero =>
      intro s b
      simp only [counter, butlast, List.zip_nil_left, trace, current]
      split
      · next h => rw [show (j - s).toNat = 0 by omega, show j = s by omega]; simp [counter, butlast, maps, sum]
      · rfl
    | succ m ih =>
      intro s b
      simp only [butlast_counter_succ, List.zip_cons_cons, trace, current]
      rw [ih (s + 1)]
      push_cast
      by_cases e1 : s + 1 ≤ j ∧ j ≤ s + 1 + m
      · rw [ite_eq_left e1, ite_eq_left (by omega), show (j - s).toNat = (j - (s + 1)).toNat + 1 by omega, sum_counter_succ]
        grind
      · rw [ite_eq_right e1]
        by_cases e2 : j = s
        · subst e2; (simp [counter, butlast, maps, sum]) <;> omega
        · rw [ite_eq_right (by omega)]; grind

-- the same with two added terms, since a higher-order summand matches a single summand only (see TODO.md)
-- (from nsqm, nsqmf, pcomp, pcompf, sqm)
theorem current_trace_prefix_sums_add (b0 : Int → Int) (n : Nat) (j : Int)
                                            (G : Int → Int) (H : Int → Int) :
  current
    (trace
       b0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 1 1 n)))
       (fun b ⟨k, i⟩ => fun j => if j = i then b k + G k + H k else b j))
    j
    = (if 0 ≤ j ∧ j ≤ integer n then
         b0 0
           + sum (maps (butlast (counter 0 1 (natural j))) (fun k => G k + H k))
       else
         b0 j) :=
  by
    rw [integer_eq, natural_eq]
    suffices g : ∀ (s : Int) (b : Int → Int), current (trace b (List.zip (butlast (counter s 1 n)) (butlast (counter (s + 1) 1 n)))
        (fun b ⟨k, i⟩ => fun j => if j = i then b k + G k + H k else b j)) j
        = (if s ≤ j ∧ j ≤ s + n then b s + sum (maps (butlast (counter s 1 (j - s).toNat)) (fun k => G k + H k)) else b j) by
      simpa using g 0 b0
    induction n with
    | zero =>
      intro s b
      simp only [counter, butlast, List.zip_nil_left, trace, current]
      split
      · next h => rw [show (j - s).toNat = 0 by omega, show j = s by omega]; simp [counter, butlast, maps, sum]
      · rfl
    | succ m ih =>
      intro s b
      simp only [butlast_counter_succ, List.zip_cons_cons, trace, current]
      rw [ih (s + 1)]
      push_cast
      by_cases e1 : s + 1 ≤ j ∧ j ≤ s + 1 + m
      · rw [ite_eq_left e1, ite_eq_left (by omega), show (j - s).toNat = (j - (s + 1)).toNat + 1 by omega, sum_counter_succ]
        grind
      · rw [ite_eq_right e1]
        by_cases e2 : j = s
        · subst e2; (simp [counter, butlast, maps, sum]) <;> omega
        · rw [ite_eq_right (by omega)]; grind

-- the special case of a constant added term
-- (from standard_seq_init_ground)
theorem current_trace_prefix_const (a0 : Int → Int) (n : Nat) (c : Int)
                                         (j : Int) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 1 1 n)))
       (fun a ⟨k, i⟩ => fun j => if j = i then a k + c else a j))
    j
    = (if 1 ≤ j ∧ j ≤ integer n then a0 0 + j * c else a0 j) :=
  by
    rw [integer_eq]
    suffices g : ∀ (s : Int) (a : Int → Int), current (trace a (List.zip (butlast (counter s 1 n)) (butlast (counter (s + 1) 1 n)))
        (fun a ⟨k, i⟩ => fun j => if j = i then a k + c else a j)) j
        = (if s + 1 ≤ j ∧ j ≤ s + n then a s + (j - s) * c else a j) by simpa using g 0 a0
    induction n with
    | zero => intro s a; (simp [counter, butlast, trace, current]) <;> omega
    | succ m ih =>
      intro s a
      simp only [butlast_counter_succ, List.zip_cons_cons, trace, current]
      rw [ih (s + 1)]
      push_cast
      by_cases e : j = s + 1
      · subst e; simp; (repeat' split) <;> grind
      · simp only [e, ite_false]; (repeat' split) <;> grind

-- sum, which is linear, and the linear transformations are moved to the outside

theorem sum_empty : sum nil = 0 :=
  by rfl

theorem sum_consts (n : Nat) (x : Int) :
  sum (butlast (consts n x)) = x * integer n :=
  by
    induction n with
    | zero => simp [consts, butlast, sum, integer]
    | succ m ih => simp [consts, butlast, sum, ih, integer]; grind

-- the sum of the first n values of a sequence that are all c, e.g. the final values of the counter of an inner loop;
-- the iteration constraint is abstracted by consts_prefix (see consts_prefix_def), since an iteration constraint as
-- a side condition does not terminate
-- (from examples/dafny/algorithms/nested_sum.dfy)
theorem sum_consts_prefix (n : Nat) (c : Int) (js : List Int)
                                (hjs : length js = n) :
  consts_prefix n c js → sum js = c * integer n :=
  by
    intro h
    rw [consts_prefix_forall] at h
    subst hjs
    rw [integer_eq]
    induction js with
    | nil => simp [sum]
    | cons j js ih =>
      simp only [sum, List.length_cons]
      rw [show j = c by simpa [earlier] using h 0 (by simp),
          ih (fun i hi => by simpa [earlier] using h (i + 1) (by simp; omega))]
      push_cast
      rw [Int.mul_add, Int.mul_one]
      omega

theorem sum_below_prefix (n : Nat) (xs : List Int) (b : Int) (c : Int)
                               (hxs : length xs = n) :
  below_prefix n xs b ∧ integer n * b ≤ c → sum xs ≤ c :=
  by
    intro ⟨h, hc⟩
    rw [below_prefix_forall] at h
    subst hxs
    rw [integer_eq] at hc
    have key : sum xs ≤ (xs.length : Int) * b := by
      clear hc
      induction xs with
      | nil => simp [sum]
      | cons x xs ih =>
        simp only [sum, List.length_cons]
        have h0 : x ≤ b := by simpa [earlier] using h 0 (by simp)
        have := ih (fun i hi => by simpa [earlier] using h (i + 1) (by simp; omega))
        push_cast
        rw [Int.add_mul, Int.one_mul]
        omega
    omega

theorem earlier_nonneg_prefix (n : Nat) (xs : List Int) (j : Nat)
                                    (hxs : length xs = n) :
  nonneg_prefix n xs ∧ integer j < integer n → earlier j xs ≤ sum xs :=
  by
    intro ⟨h, hj⟩
    rw [nonneg_prefix_forall] at h
    subst hxs
    rw [integer_eq, integer_eq] at hj
    induction xs generalizing j with
    | nil => (simp at hj) <;> omega
    | cons x xs ih =>
      have h0 : 0 ≤ x := by simpa [earlier] using h 0 (by simp)
      have hs : ∀ i : Nat, i < xs.length → 0 ≤ earlier i xs :=
        fun i hi => by simpa [earlier] using h (i + 1) (by simp; omega)
      cases j with
      | zero =>
        simp only [earlier, sum]
        have := sum_nonneg_forall xs hs
        omega
      | succ j =>
        simp only [earlier, sum]
        have := ih j hs (by simp only [List.length_cons] at hj; push_cast at hj; omega)
        omega

theorem sum_nonneg_prefix (n : Nat) (xs : List Int) (hxs : length xs = n) :
  nonneg_prefix n xs → 0 ≤ sum xs :=
  by
    intro h
    rw [nonneg_prefix_forall] at h
    subst hxs
    exact sum_nonneg_forall xs h

theorem sum_neg (values : List Int) (n : Nat)
                      (hvalues : length values = n) :
  sum (maps values (fun v => -v)) = -sum values :=
  by
    clear hvalues n
    induction values with
    | nil => rfl
    | cons v vs ih => simp [maps, sum, ih]; omega

theorem sum_scale (values : List Int) (a : Int) (n : Nat)
                        (hvalues : length values = n) :
  sum (maps values (fun v => a * v)) = a * sum values :=
  by
    clear hvalues n
    induction values with
    | nil => simp [maps, sum]
    | cons v vs ih => simp [maps, sum, ih]; grind

theorem sum_add (xs : List Int) (ys : List Int) (n : Nat)
                      (hxs : length xs = n) (hys : length ys = n) :
  sum (maps (List.zip xs ys) (fun ⟨v, w⟩ => v + w)) = sum xs + sum ys :=
  by
    induction xs generalizing ys n with
    | nil =>
      cases ys with
      | nil => simp [maps, sum]
      | cons y ys => simp at hxs hys; omega
    | cons x xs ih =>
      cases ys with
      | nil => simp at hxs hys; omega
      | cons y ys =>
        rw [List.zip_cons_cons]
        have h := ih (n := n - 1) (ys := ys) (by simp at hxs; omega) (by simp at hys; omega)
        simp only [maps, sum] at h ⊢
        omega


-- the arithmetic series, which is exact, since n * (n - 1) is even
theorem sum_counter (i : Int) (c : Int) (n : Nat) :
  sum (butlast (counter i c n)) = (2 * i + (integer n - 1) * c) * integer n / 2 :=
  by
    have h : 2 * sum (butlast (counter i c n)) = (2 * i + (integer n - 1) * c) * integer n := by
      induction n generalizing i with
      | zero => simp [counter, butlast, sum, integer]
      | succ m ih => simp only [butlast_counter_succ, sum, integer_eq] at *; push_cast; grind
    omega

-- a sum of indicators, 1 where a condition holds and 0 otherwise, is the number of values where it holds, which the
-- lemmas on counts evaluate; for one dependency and for two, as in loops with a choice
theorem sum_indicator_true {α : Type} [Inhabited α] (xs : List α)
                                                          (P : α → Prop)
                                                          (n : Nat)
                                                          (hxs : length xs = n) :
  sum (maps xs (fun x => if P x then 1 else 0))
    = count True (maps xs (fun x => P x)) :=
  by
    clear hxs n
    induction xs with
    | nil => simp [maps, sum, count]
    | cons x xs ih => simp only [maps, sum, count] at *; rw [ih]; by_cases h : P x <;> simp [h]

theorem sum_indicator_false {α : Type} [Inhabited α] (xs : List α)
                                                           (P : α → Prop)
                                                           (n : Nat)
                                                           (hxs : length xs = n) :
  sum (maps xs (fun x => if P x then 0 else 1))
    = count False (maps xs (fun x => P x)) :=
  by
    clear hxs n
    induction xs with
    | nil => simp [maps, sum, count]
    | cons x xs ih => simp only [maps, sum, count] at *; rw [ih]; by_cases h : P x <;> simp [h]

theorem sum_indicator_true_2 {α β : Type} [Inhabited α] [Inhabited β] (xs : List α)
                                                                            (ys : List β)
                                                                            (P : α → β → Prop)
                                                                            (n : Nat)
                                                                            (hxs : length xs = n)
                                                                            (hys : length ys = n) :
  sum (maps (List.zip xs ys) (fun ⟨x, y⟩ => if P x y then 1 else 0))
    = count True (maps (List.zip xs ys) (fun ⟨x, y⟩ => P x y)) :=
  by
    induction (List.zip xs ys) with
    | nil => simp [maps, sum, count]
    | cons p ps ih =>
      obtain ⟨x, y⟩ := p
      simp only [maps, sum, count] at *; rw [ih]; by_cases h : P x y <;> simp [h]

theorem sum_indicator_false_2 {α β : Type} [Inhabited α] [Inhabited β] (xs : List α)
                                                                             (ys : List β)
                                                                             (P : α → β → Prop)
                                                                             (n : Nat)
                                                                             (hxs : length xs = n)
                                                                             (hys : length ys = n) :
  sum (maps (List.zip xs ys) (fun ⟨x, y⟩ => if P x y then 0 else 1))
    = count False (maps (List.zip xs ys) (fun ⟨x, y⟩ => P x y)) :=
  by
    induction (List.zip xs ys) with
    | nil => simp [maps, sum, count]
    | cons p ps ih =>
      obtain ⟨x, y⟩ := p
      simp only [maps, sum, count] at *; rw [ih]; by_cases h : P x y <;> simp [h]

theorem sum_selects_update {α : Type} [Inhabited α] (a : α → Int) (k : α)
                                                          (v : Int)
                                                          (keys : List α)
                                                          (n : Nat)
                                                          (hkeys : length keys = n) :
  distincts keys
    → sum (selects (fun j => if j = k then v else a j) keys)
      = (if occurs k keys then
           sum (selects a keys) + v - a k
         else
           sum (selects a keys)) :=
  by
    clear hkeys n
    intro hd
    induction keys with
    | nil => simp [selects, maps, sum, occurs]
    | cons y ys ih =>
      simp only [distincts] at hd
      simp only [selects, maps, sum, occurs] at *
      rw [ih hd.2]
      by_cases e : y = k
      · subst e
        have : ¬occurs y ys := hd.1
        simp [this]
        (repeat' split) <;> omega
      · simp [e]
        (repeat' split) <;> omega

-- parity

theorem parity_selects_update {α : Type} [Inhabited α] (a : α → Int)
                                                             (k : α) (v : Int)
                                                             (keys : List α)
                                                             (n : Nat)
                                                             (hkeys : length keys = n) :
  distincts keys
    → parity (selects (fun j => if j = k then v else a j) keys)
      = (if occurs k keys then
           parity (selects a keys) + (if v % 2 = 0 then 1 else -1)
             - (if a k % 2 = 0 then 1 else -1)
         else
           parity (selects a keys)) :=
  by
    clear hkeys n
    intro hd
    induction keys with
    | nil => simp [selects, maps, parity, occurs]
    | cons y ys ih =>
      simp only [distincts] at hd
      simp only [selects, maps, parity, occurs] at *
      rw [ih hd.2]
      by_cases e : y = k
      · subst e
        have : ¬occurs y ys := hd.1
        simp [this]
        (repeat' split) <;> omega
      · simp [e]
        (repeat' split) <;> omega

-- count

theorem count_consts {α : Type} [Inhabited α] (n : Nat) (e : α) (v : α) :
  count e (butlast (consts n v)) = (if v = e then integer n else 0) :=
  by
    induction n with
    | zero => simp [consts, butlast, count, integer]
    | succ m ih => simp only [consts, butlast, count, ih, integer]; split <;> omega

-- an update of a visited key replaces its contribution, as for sum and parity
theorem count_selects_update {α β : Type} [Inhabited α] [Inhabited β] (a : α → β)
                                                                            (k : α)
                                                                            (w : β)
                                                                            (e : β)
                                                                            (keys : List α)
                                                                            (n : Nat)
                                                                            (hkeys : length keys = n) :
  distincts keys
    → count e (selects (fun j => if j = k then w else a j) keys)
      = (if occurs k keys then
           count e (selects a keys) + (if w = e then 1 else 0)
             - (if a k = e then 1 else 0)
         else
           count e (selects a keys)) :=
  by
    clear hkeys n
    intro hd
    induction keys with
    | nil => simp [selects, maps, count, occurs]
    | cons y ys ih =>
      simp only [distincts] at hd
      simp only [selects, maps, count, occurs] at *
      rw [ih hd.2]
      by_cases e : y = k
      · subst e
        have : ¬occurs y ys := hd.1
        simp [this]
        (repeat' split) <;> omega
      · simp [e]
        (repeat' split) <;> omega

-- the iterations of a counter by 1 before m and from m on, e.g. for loops with if (i < m) in the body
theorem count_true_below (m : Int) (i : Int) (n : Nat) :
  i ≤ m ∧ m ≤ i + integer n
    → count True (maps (butlast (counter i 1 n)) (fun k => k < m)) = m - i :=
  by intro ⟨h1, h2⟩; rw [(count_lt_counter m i n).1]; simp only [integer_eq] at *; omega

theorem count_false_below (m : Int) (i : Int) (n : Nat) :
  i ≤ m ∧ m ≤ i + integer n
    → count False (maps (butlast (counter i 1 n)) (fun k => k < m))
      = i + integer n - m :=
  by intro ⟨h1, h2⟩; rw [(count_lt_counter m i n).2]; simp only [integer_eq] at *; omega

theorem count_true_above (m : Int) (i : Int) (n : Nat) :
  i ≤ m ∧ m ≤ i + integer n
    → count True (maps (butlast (counter i 1 n)) (fun k => m ≤ k))
      = i + integer n - m :=
  by intro ⟨h1, h2⟩; rw [(count_le_counter m i n).1]; simp only [integer_eq] at *; omega

theorem count_false_above (m : Int) (i : Int) (n : Nat) :
  i ≤ m ∧ m ≤ i + integer n
    → count False (maps (butlast (counter i 1 n)) (fun k => m ≤ k)) = m - i :=
  by intro ⟨h1, h2⟩; rw [(count_le_counter m i n).2]; simp only [integer_eq] at *; omega

theorem count_nonnegative {α : Type} [Inhabited α] (e : α) (vs : List α) :
  0 ≤ count e vs :=
  by
    induction vs with
    | nil => simp [count]
    | cons v ws ih => simp only [count]; split <;> omega

-- the numbers 0, ..., n - 1 with the remainder r modulo m number (n + m - 1 - r) / m
-- (from half, sumt2)
theorem count_remainder (n : Nat) (m : Int) (r : Int) (hs : List Int)
                              (hhs : length hs = n) :
  0 < m ∧ 0 ≤ r ∧ r < m
    → count
      r
      (maps (List.zip (butlast (counter 0 1 n)) hs) (fun ⟨k, h⟩ => k % m))
      = (integer n + m - 1 - r) / m :=
  by
    intro ⟨hm, hr0, hrm⟩
    rw [maps_zip_fst _ hs (fun k => k % m) (by rw [length_butlast_counter, hhs]), integer_eq]
    have hr : r % m = r := Int.emod_eq_of_lt hr0 hrm
    clear hhs
    -- the count from s on: the remainder r of the values s, ..., s + n - 1 is the remainder of r - s of 0, ..., n - 1
    have gen : ∀ (s : Int), count r (maps (butlast (counter s 1 n)) (fun k => k % m))
        = ((n : Int) + m - 1 - (r - s) % m) / m := by
      induction n with
      | zero =>
        intro s
        simp only [counter, butlast, maps, count, Int.natCast_zero]
        have h1 := Int.emod_nonneg (r - s) (by omega : m ≠ 0)
        have h2 := Int.emod_lt_of_pos (r - s) hm
        rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      | succ t ih =>
        intro s
        rw [butlast_counter_succ]
        simp only [maps, count]
        rw [ih (s + 1)]
        push_cast
        have h1 := Int.emod_nonneg (r - s) (by omega : m ≠ 0)
        have h2 := Int.emod_lt_of_pos (r - s) hm
        have hq : (r - s) % m + m * ((r - s) / m) = r - s := by have := Int.emod_def (r - s) m; omega
        generalize (r - s) % m = u at *
        generalize (r - s) / m = q at *
        -- the remainder of r - (s + 1) is one less, or m - 1 after a multiple of m
        have hu1 : (r - (s + 1)) % m = if u = 0 then m - 1 else u - 1 := by
          rw [show r - (s + 1) = (u - 1) + m * q by omega, Int.add_mul_emod_self_left]
          by_cases hu : u = 0
          · subst hu
            rw [← Int.add_mul_emod_self_left (0 - 1) m 1, Int.emod_eq_of_lt (by omega) (by omega)]
            simp; omega
          · rw [Int.emod_eq_of_lt (by omega) (by omega)]
            simp [hu]
        -- s has the remainder r iff r - s is a multiple of m
        have hsr : (s % m = r) ↔ u = 0 := by
          rw [← Int.add_mul_emod_self_left s m q, show s + m * q = r - u by omega]
          constructor
          · intro h
            refine Classical.byContradiction fun hu => ?_
            by_cases hru : 0 ≤ r - u
            · rw [Int.emod_eq_of_lt hru (by omega)] at h; omega
            · rw [← Int.add_mul_emod_self_left (r - u) m 1, Int.emod_eq_of_lt (by omega) (by omega)] at h; omega
          · intro hu; subst hu; simpa using hr
        rw [hu1]
        simp only [hsr]
        by_cases hu : u = 0
        · simp only [hu, ite_true]
          rw [show ((t : Int) + m - 1 - (m - 1)) = t by omega, show ((t : Int) + 1 + m - 1 - 0) = t + 1 * m by omega,
              Int.add_mul_ediv_right _ _ (by omega)]
          omega
        · simp only [hu, ite_false]
          rw [show ((t : Int) + m - 1 - (u - 1)) = t + 1 + m - 1 - u by omega]
          omega
    have := gen 0
    simp only [Int.sub_zero, hr] at this
    exact this

-- among the truth values of a map over the n iterations, those that are false are the others than those that are
-- true; the dependencies are kept as matched, such that the counts are syntactically equal to those of the program
-- (from sumt2)
theorem count_false_true (i : Int) (c : Int) (n : Nat) (hs : List Int)
                               (P : Int → Int → Prop) (hhs : length hs = n) :
  count
    False
    (maps (List.zip (butlast (counter i c n)) hs) (fun ⟨k, h⟩ => P k h))
    = integer n
      - count
        True
        (maps (List.zip (butlast (counter i c n)) hs) (fun ⟨k, h⟩ => P k h)) :=
  by
    have hlen : (List.zip (butlast (counter i c n)) hs).length = n :=
      length_zip_eq _ _ n (length_butlast_counter i c n) hhs
    generalize List.zip (butlast (counter i c n)) hs = ps at hlen
    rw [integer_eq, ← hlen]
    clear hlen hhs
    induction ps with
    | nil => simp [maps, count]
    | cons p ps ih =>
      obtain ⟨k, h⟩ := p
      simp only [maps, count, List.length_cons] at *
      by_cases e : P k h
      · simp only [e]; simp; omega
      · simp only [e]; simp; omega


-- the iterations where a value is r are counted by the occurrences of r among the values
-- (from sumt2)
theorem count_true_eq (ks : List Int) (r : Int) (hs : List Int)
                            (F : Int → Int → Int) (n : Nat)
                            (hks : length ks = n) (hhs : length hs = n) :
  count True (maps (List.zip ks hs) (fun ⟨k, h⟩ => F k h = r))
    = count r (maps (List.zip ks hs) (fun ⟨k, h⟩ => F k h)) :=
  by
    induction (List.zip ks hs) with
    | nil => simp [maps, count]
    | cons p ps ih => obtain ⟨k, h⟩ := p; simp only [maps, count] at *; rw [ih]; by_cases e : F k h = r <;> simp [e]

-- bounds

-- the initial value is a bound of the prefix maxima and minima, which are attained by some value otherwise
theorem current_maxs_initial (x : Int) (values : List Int) (n : Nat)
                                   (hvalues : length values = n) :
  x ≤ current (maxs x values) :=
  by
    clear hvalues n
    induction values generalizing x with
    | nil => simp [maxs, trace, current]
    | cons v vs ih =>
      simp only [maxs, trace, current] at *
      have h1 := ih (if x < v then v else x)
      have h2 : x ≤ (if x < v then v else x) := by split <;> omega
      omega

theorem current_maxs_earlier (k : Nat) (x : Int) (values : List Int)
                                   (n : Nat) (hvalues : length values = n) :
  integer k < integer n → earlier k values ≤ current (maxs x values) :=
  by
    intro h
    induction values generalizing k x n with
    | nil => rw [← hvalues] at h; simp only [integer_eq, List.length_nil] at h; omega
    | cons v vs ih =>
      have e : maxs x (v :: vs) = .step x (maxs (if x < v then v else x) vs) := rfl
      rw [e]
      simp only [current]
      cases k with
      | zero =>
        simp only [earlier]
        have := current_maxs_initial (if x < v then v else x) vs vs.length rfl
        by_cases hv : x < v <;> simp only [hv, ite_true, ite_false] at this ⊢ <;> omega
      | succ i =>
        simp only [earlier]
        exact ih i _ vs.length rfl (by simp at hvalues; simp only [integer_eq] at h ⊢; omega)

theorem current_mins_initial (x : Int) (values : List Int) (n : Nat)
                                   (hvalues : length values = n) :
  current (mins x values) ≤ x :=
  by
    clear hvalues n
    induction values generalizing x with
    | nil => simp [mins, trace, current]
    | cons v vs ih =>
      simp only [mins, trace, current] at *
      have h1 := ih (if v < x then v else x)
      have h2 : (if v < x then v else x) ≤ x := by split <;> omega
      omega

theorem current_mins_earlier (k : Nat) (x : Int) (values : List Int)
                                   (n : Nat) (hvalues : length values = n) :
  integer k < integer n → current (mins x values) ≤ earlier k values :=
  by
    intro h
    induction values generalizing k x n with
    | nil => rw [← hvalues] at h; simp only [integer_eq, List.length_nil] at h; omega
    | cons v vs ih =>
      have e : mins x (v :: vs) = .step x (mins (if v < x then v else x) vs) := rfl
      rw [e]
      simp only [current]
      cases k with
      | zero =>
        simp only [earlier]
        have := current_mins_initial (if v < x then v else x) vs vs.length rfl
        by_cases hv : v < x <;> simp only [hv, ite_true, ite_false] at this ⊢ <;> omega
      | succ i =>
        simp only [earlier]
        exact ih i _ vs.length rfl (by simp at hvalues; simp only [integer_eq] at h ⊢; omega)

-- a value that increases by a positive constant in each of its three cases exceeds its initial value after at
-- least one iteration
-- (from large_const)
theorem current_trace_increasing (x0 : Int) (n : Nat) (a : Int) (b : Int)
                                       (c : Int) (hs : List Int)
                                       (C : Int → Prop) (D : Int → Prop)
                                       (E : Int → Prop) (hhs : length hs = n) :
  n ≠ zero ∧ 0 < a ∧ 0 < b ∧ 0 < c
    → x0
      < current
        (trace
           x0
           (List.zip (butlast (counter 0 1 n)) hs)
           (fun x ⟨k, h⟩ =>
              if C h then x + a else if D h then x + b else x + c)) :=
  by
    intro ⟨hn, ha, hb, hc⟩
    have hstrict : ∀ (x : Int) (p : Int × Int),
        x < (fun x (p : Int × Int) => match p with | (k, h) => if C h then x + a else if D h then x + b else x + c) x p := by
      intro x ⟨k, h⟩
      show x < (if C h then x + a else if D h then x + b else x + c)
      split
      · omega
      · split <;> omega
    cases n with
    | zero => exact absurd rfl hn
    | succ m =>
      cases hs with
      | nil => simp at hhs
      | cons h hs =>
        rw [butlast_counter_succ, List.zip_cons_cons]
        simp only [trace, current]
        exact Int.lt_of_lt_of_le (hstrict x0 (0, h)) (trace_mono _ _ _ (fun x p => Int.le_of_lt (hstrict x p)))

-- an interval that contains the initial value and that each of the three cases maps into itself contains the
-- current value, an inductive invariant; the left-hand side is the conjunction of both bounds, which binds both
-- (from benchmark51_polynomial)
theorem current_trace_bounded (x0 : Int) (n : Nat) (lo : Int) (hi : Int)
                                    (C1 : Int → Prop) (C2 : Int → Prop)
                                    (C3 : Int → Prop) (F1 : Int → Int)
                                    (F2 : Int → Int) (F3 : Int → Int) :
  lo ≤ x0
    ∧ x0 ≤ hi
    ∧ (∀ (y : Int), lo ≤ y ∧ y ≤ hi ∧ C1 y → lo ≤ F1 y ∧ F1 y ≤ hi)
    ∧ (∀ (y : Int), lo ≤ y ∧ y ≤ hi ∧ C2 y → lo ≤ F2 y ∧ F2 y ≤ hi)
    ∧ (∀ (y : Int), lo ≤ y ∧ y ≤ hi ∧ C3 y → lo ≤ F3 y ∧ F3 y ≤ hi)
    ∧ (∀ (y : Int), ¬C1 y ∧ ¬C2 y → C3 y)
    → (lo
         ≤ current
           (trace
              x0
              (butlast (counter 0 1 n))
              (fun x k => if C1 x then F1 x else if C2 x then F2 x else F3 x))
         ∧ current
           (trace
              x0
              (butlast (counter 0 1 n))
              (fun x k => if C1 x then F1 x else if C2 x then F2 x else F3 x))
           ≤ hi
         ↔ True) :=
  by
    intro ⟨h1, h2, f1, f2, f3, hc⟩
    simp only [iff_true]
    suffices g : ∀ s x, lo ≤ x ∧ x ≤ hi → lo ≤ current (trace x (butlast (counter s 1 n))
        (fun x k => if C1 x then F1 x else if C2 x then F2 x else F3 x)) ∧ current (trace x (butlast (counter s 1 n))
        (fun x k => if C1 x then F1 x else if C2 x then F2 x else F3 x)) ≤ hi from g 0 x0 ⟨h1, h2⟩
    induction n with
    | zero => intro s x hx; simpa [counter, butlast, trace, current] using hx
    | succ m ih =>
      intro s x hx
      simp only [butlast_counter_succ, trace, current]
      apply ih
      by_cases c1 : C1 x
      · rw [ite_eq_left c1]; exact f1 x ⟨hx.1, hx.2, c1⟩
      · rw [ite_eq_right c1]
        by_cases c2 : C2 x
        · rw [ite_eq_left c2]; exact f2 x ⟨hx.1, hx.2, c2⟩
        · rw [ite_eq_right c2]; exact f3 x ⟨hx.1, hx.2, hc x ⟨c1, c2⟩⟩

-- which is instantiated at the positions j in the range
-- (from simple_array_index_value_2)
theorem earlier_above_iterations (n : Nat) (j : Nat) (ts : List Int) :
  above_iterations n ts ∧ integer j < integer n
    → (integer j < earlier j ts ↔ True) :=
  by
    intro ⟨h, hj⟩
    simp only [iff_true]
    simp only [integer_eq] at hj
    induction n with
    | zero => omega
    | succ m ih =>
      simp only [above_iterations] at h
      by_cases e : j = m
      · subst e; simpa [integer_eq] using h.2
      · exact ih h.1 (by omega)

-- arithmetic, in the normal form of the simplifier

-- even summands do not change the remainder modulo 2
-- (from array_monotonic, phases_1-1, phases_1-2)
theorem mod_add_even (x : Int) (n : Int) : (x + 2 * n) % 2 = x % 2 :=
  by omega

-- a positive number divides itself
-- (from modn, modnf)
theorem mod_self (x : Int) : 0 < x → x % x = 0 :=
  by intro h; exact Int.emod_self

-- division of a multiple of m plus a remainder below m
-- (from half)
theorem div_quotient_remainder (m : Int) (k : Int) (r : Int) :
  0 < m ∧ 0 ≤ r ∧ r < m → (m * k + r) / m = k :=
  by
    intro ⟨hm, hr, hr'⟩
    rw [Int.add_comm, Int.add_mul_ediv_left r k (by omega), Int.ediv_eq_zero_of_lt hr hr']
    omega

-- twice a number is the product of consecutive numbers iff it is its half, as an equivalence of atoms, since an
-- equation of integers as a lemma rewrites its left-hand side as a term
-- (from gauss_sum)
theorem double_eq_half (n : Int) (s : Int) :
  2 * s = n + n * n ↔ s = (n + n * n) / 2 :=
  by
    have h : (n + n * n) % 2 = 0 := by
      have : n * n % 2 = n % 2 := by
        rcases Int.emod_two_eq n with h | h <;> simp [Int.mul_emod, h]
      omega
    omega

-- the sum 0 + 1 + ... + (n - 1) plus 1 is at least n
-- (from afnp2014)
theorem triangle_bound (n : Int) : n ≤ (-n + n * n) / 2 + 1 :=
  by
    have h : 0 ≤ (n - 1) * (n - 2) := by
      rcases Int.lt_or_le 1 n with h | h
      · exact Int.mul_nonneg (by omega) (by omega)
      · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    have e : (n - 1) * (n - 2) = n * n - 3 * n + 2 := by grind
    omega

-- division by 2 of polynomials with even coefficients, since a generic (2 * a + 2 * b) / 2 does not match literal
-- coefficients
-- (from eqn1, eqn1f)
theorem half_2x_2xx (x : Int) : (2 * x + 2 * x * x) / 2 = x + x * x :=
  by
    have : 2 * x * x = 2 * (x * x) := by grind
    omega

-- the same
-- (from nsqm, nsqmf, sqm)
theorem half_4x_2xx (x : Int) : (4 * x + 2 * x * x) / 2 = 2 * x + x * x :=
  by
    have : 2 * x * x = 2 * (x * x) := by grind
    omega

-- the same
-- (from pcomp, pcompf)
theorem half_6x_6xx (x : Int) :
  (6 * x + 6 * x * x) / 2 = 3 * x + 3 * x * x :=
  by
    have : 6 * x * x = 6 * (x * x) := by grind
    have : 3 * x * x = 3 * (x * x) := by grind
    omega

theorem half_4x_4xx (x : Int) :
  (4 * x + 4 * x * x) / 2 = 2 * x + 2 * x * x :=
  by
    have : 4 * x * x = 4 * (x * x) := by grind
    have : 2 * x * x = 2 * (x * x) := by grind
    omega

theorem half_2x (x : Int) : 2 * x / 2 = x :=
  by omega

theorem third_3x (x : Int) : 3 * x / 3 = x :=
  by omega

theorem triangle_nonneg (x : Int) : 0 ≤ (x + x * x) / 2 :=
  by
    have h : 0 ≤ x * (x + 1) := by
      rcases Int.lt_or_le x 0 with h | h
      · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · exact Int.mul_nonneg h (by omega)
    have e : x * (x + 1) = x + x * x := by grind
    omega

theorem triangle_nonneg_below (x : Int) : 0 ≤ (-x + x * x) / 2 :=
  by
    have h : 0 ≤ x * (x - 1) := by
      rcases Int.lt_or_le x 1 with h | h
      · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · exact Int.mul_nonneg (by omega) (by omega)
    have e : x * (x - 1) = -x + x * x := by grind
    omega

theorem triangle_nonneg_add (x : Int) (d : Int) :
  0 ≤ d → 0 ≤ (x + x * x) / 2 + d :=
  by intro h; have := triangle_nonneg x; omega

theorem triangle_nonneg_below_add (x : Int) (d : Int) :
  0 ≤ d → 0 ≤ (-x + x * x) / 2 + d :=
  by intro h; have := triangle_nonneg_below x; omega

theorem div_below (b : Int) (x : Int) (d : Int) :
  0 < d ∧ 0 ≤ x ∧ x < d * (b + 1) → (b < x / d ↔ False) :=
  by
    intro ⟨hd, _, hx⟩
    have : x / d < b + 1 := Int.ediv_lt_of_lt_mul hd (by rw [Int.mul_comm] at hx; exact hx)
    simp only [iff_false]
    omega

theorem mod_two_not_zero (y : Int) : y % 2 ≠ 0 ↔ y % 2 = 1 :=
  by constructor <;> intro h <;> omega

-- the differences (k + 1)^3 - k^3 - 1 = 3 * k + 3 * k * k telescope to n^3 - n; teq.dfy splits such a sum by linearity
-- first, hence the sum of 3 * k * k as the rest, such that the division atoms cancel
-- (from pcomp, pcompf)
theorem sum_squares (n : Nat) :
  sum (maps (butlast (counter 0 1 n)) (fun k => 3 * k * k))
    = integer n * integer n * integer n - integer n
      - 3 * ((-integer n + integer n * integer n) / 2) :=
  by
    rw [integer_eq]
    have snoc : ∀ (s : Int) (t : Nat) (F : Int → Int), sum (maps (butlast (counter s 1 (t + 1))) F)
        = sum (maps (butlast (counter s 1 t)) F) + F (s + t) := by
      intro s t F
      induction t generalizing s with
      | zero => simp [counter, butlast, maps, sum]
      | succ u ih => rw [sum_counter_succ, ih (s + 1), sum_counter_succ]; push_cast; grind
    have half : ∀ (n : Int), (-n + n * n) % 2 = 0 := by
      intro n
      have : n * n % 2 = n % 2 := by rcases Int.emod_two_eq n with h | h <;> simp [Int.mul_emod, h]
      omega
    induction n with
    | zero => simp [counter, butlast, maps, sum]
    | succ m ih =>
      rw [snoc, ih]
      push_cast
      have h1 := half m
      have h2 := half (m + 1)
      grind

-- a power of 2 is not divisible by 3
-- (from underapprox_1-1, underapprox_1-2)
theorem pow_two_mod_three (n : Nat) : pow 2 n % 3 = 0 ↔ False :=
  by
    have h : pow 2 n % 3 = 1 ∨ pow 2 n % 3 = 2 := by
      induction n with
      | zero => simp [pow]
      | succ m ih => simp only [pow]; omega
    simp; omega

-- a nonnegative factor cancels in a strict comparison; does not match a literal coefficient (see TODO.md)
-- (from count_by_k)
theorem mul_lt_cancel (k : Int) (a : Int) (b : Int) :
  0 ≤ k → (k * a < k * b ↔ 0 < k ∧ a < b) :=
  by
    intro hk
    constructor
    · intro h
      have hk' : 0 < k := by
        rcases Int.lt_or_eq_of_le hk with h' | h'
        · exact h'
        · subst h'; simp at h
      exact ⟨hk', Int.lt_of_mul_lt_mul_left h hk⟩
    · intro ⟨hk', h⟩; exact Int.mul_lt_mul_of_pos_left h hk'

-- (invs_two_phases stands here, after prefix_counter and current_trace_two_phases, which its proof uses)
-- the same counter is increasing for 0 < c, hence an upper bound B holds at all its values before the current one
-- iff it holds at the last of them
-- (from Mono1_1-2)
theorem invs_two_phases (x0 : Int) (n : Nat) (b : Int) (c : Int)
                              (B : Int) :
  x0 ≤ b ∧ 0 < c
    → (invs
         (List.zip (butlast (counter 0 1 n)) (butlast
                                                (trace
                                                   x0
                                                   (butlast (counter 0 1 n))
                                                   (fun x k =>
                                                      if x < b then
                                                        x + 1
                                                      else
                                                        x + c))))
         (fun ⟨k, x⟩ => x < B)
         ↔ n = zero
           ∨ (if integer n - 1 ≤ b - x0 then
                x0 + integer n - 1
              else
                b + (integer n - 1 - (b - x0)) * c)
             < B) :=
  by
    intro ⟨hx, hc⟩
    -- the values before the current one are the results g i of the first i iterations, which do not decrease,
    -- hence the bound holds for all of them iff it holds for the last one, whose closed form is current_trace_two_phases
    have hlen : (butlast (trace x0 (butlast (counter 0 1 n)) (fun x k => if x < b then x + 1 else x + c))).length = n := by
      rw [length_butlast_trace, length_butlast_counter]
    refine (invs_zip_counter 0 n _ hlen (fun k x => x < B)).trans ?_
    have hg : ∀ i : Nat, i < n →
        earlier i (butlast (trace x0 (butlast (counter 0 1 n)) (fun x k => if x < b then x + 1 else x + c)))
        = current (trace x0 (butlast (counter 0 1 i)) (fun x k => if x < b then x + 1 else x + c)) := by
      intro i hi
      rw [earlier_butlast_trace i x0 _ _ (by rw [length_butlast_counter]; exact hi),
          prefix_counter i 0 1 n (by simp only [integer_eq]; omega)]
    have snoc : ∀ (i : Nat) (x s : Int),
        current (trace x (butlast (counter s 1 (i + 1))) (fun x k => if x < b then x + 1 else x + c))
        = (fun x => if x < b then x + 1 else x + c)
            (current (trace x (butlast (counter s 1 i)) (fun x k => if x < b then x + 1 else x + c))) := by
      intro i
      induction i with
      | zero => intro x s; simp [counter, butlast, trace, current]
      | succ u ih =>
        intro x s
        rw [butlast_counter_succ, butlast_counter_succ]
        simp only [trace, current]
        exact ih _ (s + 1)
    have mono : ∀ (i d : Nat),
        current (trace x0 (butlast (counter 0 1 i)) (fun x k => if x < b then x + 1 else x + c))
        ≤ current (trace x0 (butlast (counter 0 1 (i + d))) (fun x k => if x < b then x + 1 else x + c)) := by
      intro i d
      induction d with
      | zero => exact Int.le_refl _
      | succ e ih =>
        rw [show i + (e + 1) = (i + e) + 1 by omega, snoc]
        refine Int.le_trans ih ?_
        show _ ≤ (if current _ < b then current _ + 1 else current _ + c)
        split <;> omega
    cases n with
    | zero => simp
    | succ t =>
      have hfalse : (t + 1 = zero) = False := by simp
      have hlast := current_trace_two_phases x0 t b c ⟨hx, Int.le_of_lt hc⟩
      have e : integer (t + 1) - 1 = integer t := by simp only [integer_eq]; push_cast; omega
      rw [hfalse, false_or, show x0 + integer (t + 1) - 1 = x0 + (integer (t + 1) - 1) by omega, e, ← hlast]
      constructor
      · intro h
        have := h t (by omega)
        rw [hg t (by omega)] at this
        exact this
      · intro h i hi
        show earlier i _ < B
        rw [hg i hi]
        have := mono i (t - i)
        rw [show i + (t - i) = t by omega] at this
        exact Int.lt_of_le_of_lt this h

-- counterexamples: the lemmas without the assumptions above, which the contexts of the goals of -teq provide,
-- e.g. a prefix that is not longer than the other one, or a nonempty list

-- prefix_prefix for j > k
example : ¬ («prefix» 2 («prefix» 1 [(1 : Int), 2]) = «prefix» 2 [1, 2]) :=
  by simp [«prefix»]

-- occurs_earlier for the empty sequence
example : ¬ (occurs (earlier 0 ([] : List Int)) []) :=
  by simp [occurs]

-- prefix_counter and prefix_consts for k > n, where the prefix is as long as the list
example : ¬ («prefix» 1 (butlast (counter 0 1 0)) = butlast (counter 0 1 1)) :=
  by simp [«prefix», counter, butlast]

example : ¬ («prefix» 1 (butlast (consts 0 (0 : Int))) = butlast (consts 1 0)) :=
  by simp [«prefix», consts, butlast]

-- maps_earlier for a list that is longer than the iterations
example : ¬ (maps (butlast (counter 0 1 0)) (fun k => earlier (natural k) [(1 : Int)]) = [1]) :=
  by simp [maps, counter, butlast]

-- the following hold only for dependencies of equal length (see TODO.md), here a further dependency that is shorter
-- than the iterations, which zip truncates

-- sum_add
example : ¬ (sum (maps (List.zip [(1 : Int)] ([] : List Int)) (fun ⟨v, w⟩ => v + w)) = sum [1] + sum []) :=
  by simp [maps, sum]

-- count_false_true
example : ¬ (count False (maps (List.zip (butlast (counter 0 1 1)) ([] : List Int)) (fun ⟨k, h⟩ => k < h))
    = integer 1 - count True (maps (List.zip (butlast (counter 0 1 1)) ([] : List Int)) (fun ⟨k, h⟩ => k < h))) :=
  by simp [maps, count, counter, butlast, integer]

-- count_remainder
example : ¬ (count (0 : Int) (maps (List.zip (butlast (counter 0 1 1)) ([] : List Int)) (fun ⟨k, h⟩ => k % 1))
    = (integer 1 + 1 - 1 - 0) / 1) :=
  by simp [maps, count, counter, butlast, integer]

-- invs_counter_positive_last
example : ¬ (invs (List.zip ([] : List Int) (List.zip ([] : List Int) (butlast (counter 0 0 1)))) (fun ⟨h, g, x⟩ => 0 < x + 0)
    ↔ (1 : Nat) = zero ∨ 0 < (0 : Int) + 0 ∧ 0 < 0 + (integer 1 - 1) * 0 + 0) :=
  by simp [invs]

-- invs_counter_positive_middle
example : ¬ (invs (List.zip ([] : List Int) (List.zip (butlast (counter 0 0 1)) ([] : List Int))) (fun ⟨h, x, g⟩ => 0 < x + 0)
    ↔ (1 : Nat) = zero ∨ 0 < (0 : Int) + 0 ∧ 0 < 0 + (integer 1 - 1) * 0 + 0) :=
  by simp [invs]

-- agree_prefix_def
example : ¬ (invs (List.zip (butlast (counter 0 1 1)) ([] : List Int))
      (fun ⟨k, h⟩ => earlier (natural k) [(1 : Int)] = earlier (natural k) [2])
    ↔ agree_prefix 1 [1] [2]) :=
  by simp [invs, agree_prefix, earlier]

-- not_occurs_prefix_def
example : ¬ (invs (List.zip (butlast (counter 0 1 1)) ([] : List Int)) (fun ⟨k, h⟩ => earlier (natural k) [(1 : Int)] ≠ 1)
    ↔ ¬occurs 1 («prefix» 1 [(1 : Int)])) :=
  by simp [invs, occurs, «prefix»]

-- above_iterations_def
example : ¬ (invs (List.zip (butlast (counter 0 1 1)) (List.zip ([] : List Int) [(0 : Int)])) (fun ⟨k, h, t⟩ => k < t)
    ↔ above_iterations 1 [0]) :=
  by simp [invs, above_iterations, earlier, integer]

-- consts_prefix_def
example : ¬ (invs (List.zip (butlast (counter 0 1 1)) ([] : List Int)) (fun ⟨k, h⟩ => earlier (natural k) [(1 : Int)] = 2)
    ↔ consts_prefix 1 2 [1]) :=
  by simp [invs, consts_prefix, earlier]

-- sum_consts_prefix for a list that is longer than the iterations
example : ¬ (consts_prefix 1 1 [(1 : Int), 1] → sum [1, 1] = 1 * integer 1) :=
  by simp [consts_prefix, earlier, sum, integer_eq]

-- current_trace_cap
example : ¬ (current (trace (fun (_ : Int) => (1 : Int)) (List.zip (butlast (counter 0 1 1)) ([] : List Int))
      (fun a ⟨k, h⟩ => if a k < 0 then a else fun j => if j = k then 0 else a j)) 0
    = (if 0 ≤ (0 : Int) ∧ 0 < integer 1 ∧ 0 ≤ (1 : Int) then 0 else 1)) :=
  by simp [trace, current, integer]

-- current_trace_increasing
example : ¬ ((1 : Nat) ≠ zero ∧ (0 : Int) < 1 ∧ (0 : Int) < 1 ∧ (0 : Int) < 1
    → (0 : Int) < current (trace 0 (List.zip (butlast (counter 0 1 1)) ([] : List Int))
        (fun x ⟨k, h⟩ => if h < 0 then x + 1 else if h = 0 then x + 1 else x + 1))) :=
  by simp [trace, current]

-- selects_stores and selects_stores_counter, with fewer values than keys
example : ¬ (distincts [(0 : Int)] → selects (current (stores (fun (_ : Int) => (0 : Int)) [0] [])) [0] = []) :=
  by simp [distincts, occurs, selects, maps, stores, trace, current]

-- current_trace_conditional_store_distinct, with more positions than iterations
example : ¬ (distincts [(0 : Int)] → current (trace (fun (_ : Int) => (0 : Int)) (List.zip (butlast (counter 0 1 0)) (List.zip [(0 : Int)] [(0 : Int)]))
      (fun a ⟨k, p, c⟩ => if True then fun j => if j = p then 1 else a j else a)) 0
    = (if occurs 0 [(0 : Int)] ∧ True then 1 else 0)) :=
  by simp [distincts, occurs, trace, current, counter, butlast]

-- current_trace_conditional_store_deps
example : ¬ (current (trace (fun (_ : Int) => (0 : Int)) (List.zip (butlast (counter 0 1 1)) (List.zip ([] : List Int) (List.zip ([] : List Int) ([] : List Int))))
      (fun a ⟨k, h, c, v⟩ => if True then fun j => if j = k then 1 else a j else a)) 0
    = (if 0 ≤ (0 : Int) ∧ 0 < integer 1 ∧ True then 1 else 0)) :=
  by simp [trace, current, integer]

-- current_trace_bounded, where the updates are conditionals that apply F3 also if no guard holds, unlike the cases of
-- teq.dfy, whose guards are complete
example : ¬ ((0 : Int) ≤ 0 ∧ (0 : Int) ≤ 0
    ∧ (∀ (y : Int), 0 ≤ y ∧ y ≤ 0 ∧ False → 0 ≤ y ∧ y ≤ 0)
    ∧ (∀ (y : Int), 0 ≤ y ∧ y ≤ 0 ∧ False → 0 ≤ y ∧ y ≤ 0)
    ∧ (∀ (y : Int), 0 ≤ y ∧ y ≤ 0 ∧ False → 0 ≤ (5 : Int) ∧ (5 : Int) ≤ 0)
    → (0 ≤ current (trace 0 (butlast (counter 0 1 1)) (fun x k => if False then x else if False then x else 5))
        ∧ current (trace 0 (butlast (counter 0 1 1)) (fun x k => if False then x else if False then x else 5)) ≤ 0
        ↔ True)) :=
  by simp [trace, current, counter, butlast]

end TEQ
