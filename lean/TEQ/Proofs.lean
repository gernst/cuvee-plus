-- the proofs of the lemmas of the database (Database.lean), each a theorem of the name of the lemma whose statement is
-- that of Stmt.<name> (checked in Check.lean), with the auxiliary lemmas they need (the theorems of the former legacy
-- database were removed on Oct 23, 2026)
import TEQ.Database

open Classical

set_option linter.unusedVariables false

noncomputable section

namespace TEQ

open Nat (zero succ)
open List (nil cons length)
open Trace

-- naturals: their values as integers, which the arithmetic of the simplifier reasons about, and back

-- auxiliary lemmas of the proofs
-- integer and natural are the conversions of Lean
theorem integer_cast (n : Nat) : integer n = (n : Int) := by
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
-- the printer writes the cases of an update as conditionals whose last branch, where no guard holds, is unspecified
-- (lean.Printer); for complementary guards that branch is dead, which these lemmas drop, for any instances of
-- decidability (open Classical mixes them)
@[simp] theorem ite_lt_le {α : Type} (a b : Int) (h1 : Decidable (a < b)) (h2 : Decidable (b ≤ a)) (p q z : α) :
    @ite α (a < b) h1 p (@ite α (b ≤ a) h2 q z) = @ite α (a < b) h1 p q := by
  by_cases h : a < b
  · simp [h]
  · rw [if_neg h, if_neg h, if_pos (by omega)]

@[simp] theorem ite_le_lt {α : Type} (a b : Int) (h1 : Decidable (a ≤ b)) (h2 : Decidable (b < a)) (p q z : α) :
    @ite α (a ≤ b) h1 p (@ite α (b < a) h2 q z) = @ite α (a ≤ b) h1 p q := by
  by_cases h : a ≤ b
  · simp [h]
  · rw [if_neg h, if_neg h, if_pos (by omega)]

@[simp] theorem ite_eq_ne {α β : Type} (a b : β) (h1 : Decidable (a = b)) (h2 : Decidable (a ≠ b)) (p q z : α) :
    @ite α (a = b) h1 p (@ite α (a ≠ b) h2 q z) = @ite α (a = b) h1 p q := by
  by_cases h : a = b
  · simp [h]
  · rw [if_neg h, if_neg h, if_pos h]

@[simp] theorem ite_not_else {α : Type} (c : Prop) (h1 : Decidable c) (h2 : Decidable (¬c)) (p q z : α) :
    @ite α c h1 p (@ite α (¬c) h2 q z) = @ite α c h1 p q := by
  by_cases h : c
  · simp [h]
  · rw [if_neg h, if_neg h, if_pos h]

@[simp] theorem ite_ne_eq {α β : Type} (a b : β) (h1 : Decidable (a ≠ b)) (h2 : Decidable (a = b)) (p q z : α) :
    @ite α (a ≠ b) h1 p (@ite α (a = b) h2 q z) = @ite α (a ≠ b) h1 p q := by
  by_cases h : a = b <;> simp [h]

@[simp] theorem ite_not_first {α : Type} (c : Prop) (h1 : Decidable (¬c)) (h2 : Decidable c) (p q z : α) :
    @ite α (¬c) h1 p (@ite α c h2 q z) = @ite α (¬c) h1 p q := by
  by_cases h : c <;> simp [h]

theorem butlast_counter_succ (i c : Int) (m : Nat) :
    butlast (counter i c (m + 1)) = i :: butlast (counter (i + c) c m) := rfl

theorem trace_zip_self {α β : Type} (x : α) (l : List β) (g : α → β × β → α) :
    trace x (List.zip l l) g = trace x l (fun a k => g a (k, k)) := by
  induction l generalizing x with
  | nil => rfl
  | cons k l ih => show Trace.step x (trace (g x (k, k)) (List.zip l l) g) = Trace.step x _; rw [ih]

-- updates that agree on the values s, ..., s + n - 1 of a counter give the same trace over it, e.g. where guards are
-- complementary on the values of the counter only (k == 0 and 0 < k for k from 0)
theorem trace_counter_congr {α β : Type} (x : α) (s : Int) (n : Nat) (ys : List β) (f g : α → Int × β → α)
    (h : ∀ a k y, s ≤ k → k < s + n → f a (k, y) = g a (k, y)) :
    trace x (List.zip (butlast (counter s 1 n)) ys) f = trace x (List.zip (butlast (counter s 1 n)) ys) g := by
  induction n generalizing x s ys with
  | zero => rfl
  | succ n ih =>
    cases ys with
    | nil => simp [List.zip_nil_right, trace]
    | cons y ys =>
      rw [butlast_counter_succ, List.zip_cons_cons]
      simp only [trace]
      rw [h x s y (by omega) (by omega), ih _ (s + 1) ys (fun a k y h1 h2 => h a k y (by omega) (by omega))]

theorem length_butlast_counter (i c : Int) (n : Nat) : (butlast (counter i c n)).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ m ih => simp [butlast_counter_succ, ih]

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
    count True (maps (butlast (counter i 1 n)) (fun k => k < m)) = Max.max 0 (Min.min (n : Int) (m - i)) ∧
    count False (maps (butlast (counter i 1 n)) (fun k => k < m)) = (n : Int) - Max.max 0 (Min.min (n : Int) (m - i)) := by
  induction n generalizing i with
  | zero => (simp [counter, butlast, maps, count]) <;> omega
  | succ k ih =>
    simp only [butlast_counter_succ, maps, count]
    rw [(ih (i + 1)).1, (ih (i + 1)).2]
    by_cases h : i < m <;> simp [h] <;> omega

theorem count_le_counter (m i : Int) (n : Nat) :
    count True (maps (butlast (counter i 1 n)) (fun k => m ≤ k)) = (n : Int) - Max.max 0 (Min.min (n : Int) (m - i)) ∧
    count False (maps (butlast (counter i 1 n)) (fun k => m ≤ k)) = Max.max 0 (Min.min (n : Int) (m - i)) := by
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

-- a sum of t terms, each at most b, is at most t * b
theorem sum_counter_le (s : Int) (t : Nat) (f : Int → Int) (b : Int) (h : ∀ k, s ≤ k → k < s + t → f k ≤ b) :
    sum (maps (butlast (counter s 1 t)) f) ≤ t * b := by
  induction t generalizing s with
  | zero => simp [counter, butlast, maps, sum]
  | succ t ih =>
    rw [sum_counter_succ]
    have h1 := h s (by omega) (by push_cast; omega)
    have h2 := ih (s + 1) (fun k hk1 hk2 => h k (by omega) (by push_cast; omega))
    calc f s + sum (maps (butlast (counter (s + 1) 1 t)) f) ≤ b + t * b := Int.add_le_add h1 h2
      _ = ((t + 1 : Nat) : Int) * b := by push_cast; rw [Int.add_mul, Int.one_mul, Int.add_comm]


theorem natural_integer (n : Nat) : natural (integer n) = n :=
  by simp [natural_eq, integer_cast]

theorem integer_natural_facts : Stmt.integer_natural_facts := by
  intro n
  exact ⟨by rw [integer_cast]; omega, natural_integer n⟩

theorem integer_natural (x : Int) : 0 ≤ x → integer (natural x) = x :=
  by intro h; simp [natural_eq, integer_cast]; omega

theorem zero_integer (n : Nat) : integer n = 0 ↔ n = zero :=
  by cases n <;> simp [integer_cast] <;> omega

theorem zero_integer_value (n : Nat) : n = zero → integer n = 0 :=
  (zero_integer n).2

-- loops whose numbers of iterations have the same value, e.g. N for loops in sequence, iterate equally often
-- (from ss1)
theorem integer_injective (m : Nat) (n : Nat) :
  integer m = integer n ↔ m = n :=
  by simp only [integer_cast]; constructor <;> intro h <;> omega

-- the number of iterations of an inner loop determined by its value, e.g. by the test and the exit of the loop
theorem integer_eq (n : Nat) (x : Int) :
  0 ≤ x → (integer n = x ↔ n = natural x) :=
  by intro h; simp only [integer_cast, natural_eq]; omega

-- small constants as naturals and back, e.g. the iterations of loops with literal bounds, and indices of reads
-- the natural of a value that is not positive is zero, e.g. the iterations of a loop that does not run
theorem natural_nonpositive (x : Int) : x ≤ 0 → natural x = zero :=
  by intro h; simp [natural_eq]; omega

theorem natural_positive (x : Int) : 0 < x → natural x ≠ zero :=
  by intro h; rw [natural_eq]; show x.toNat ≠ 0; omega

theorem natural_zero : natural 0 = zero :=
  by simp [natural_eq]

theorem integer_zero : integer zero = 0 :=
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

-- a loop that updates each position once, from s on, by a function of the old value, stores the values computed
-- from the array before the loop, as long as the positions from s on still hold them
theorem stores_counter_read (a0 : Int → Int) (F : Int → Int → Int) : ∀ (m : Nat) (s : Int) (b : Int → Int),
    (∀ x, s ≤ x → b x = a0 x) →
    trace b (List.zip (butlast (counter s 1 m)) (butlast (counter s 1 m)))
      (fun a ⟨k, i⟩ => fun j => if j = k then F k (a k) else a j)
    = stores b (butlast (counter s 1 m)) (maps (butlast (counter s 1 m)) (fun k => F k (a0 k))) := by
  intro m
  induction m with
  | zero => intro s b _; simp [counter, butlast, trace, stores, maps]
  | succ t ih =>
    intro s b hb
    simp only [butlast_counter_succ, List.zip_cons_cons, maps, stores, trace] at ih ⊢
    rw [hb s (by omega)]
    congr 1
    exact ih (s + 1) _ (by intro x hx; simp [show x ≠ s by omega, hb x (by omega)])

-- a loop that updates each position once, by cases on its old value, stores the values computed from the initial
-- array
-- (from MonoCera: conda, s1lif-s5lif)
theorem stores_cases_def_complete (a0 : Int → Int) (n : Nat) (c : Int)
                               (P : Int → Prop) (G : Int → Int) :
  trace
    a0
    (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
    (fun a ⟨k, i⟩ =>
       if P (a k) then
         fun j => if j = k then c else a j
       else
         fun j => if j = k then G (a k) else a j)
    = stores
      a0
      (butlast (counter 0 1 n))
      (maps
         (butlast (counter 0 1 n))
         (fun k => if P (a0 k) then c else G (a0 k))) :=
  by
    have := stores_counter_read a0 (fun _ v => if P v then c else G v) n 0 a0 (fun _ _ => rfl)
    simp only at this
    rw [← this]
    congr 1
    funext a p j
    by_cases h : P (a p.1) <;> by_cases e : j = p.1 <;> simp [h, e]

-- the former statement over the counter twice (trace_zip_self)
theorem stores_cases_zip :
  ∀ (a0 : Int → Int) (n : Nat) (c : Int) (P : Int → Prop) (G : Int → Int),
    trace
      a0
      (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
      (fun a ⟨k, i⟩ =>
         if P (a k) then
           fun j => if j = k then c else a j
         else
           if ¬P (a k) then
             fun j => if j = k then G (a k) else a j
           else
             unspecified)
      = stores
        a0
        (butlast (counter 0 1 n))
        (maps
           (butlast (counter 0 1 n))
           (fun k => if P (a0 k) then c else G (a0 k))) := by
  intro a0 n c P G
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact stores_cases_def_complete a0 n c P G

theorem stores_cases : Stmt.stores_cases := by
  intro a0 n c P G
  have h := stores_cases_zip a0 n c P G
  rw [trace_zip_self] at h
  exact h

-- a loop that stores at each position k a constant chosen by cases on k stores these values
-- (from MonoCera: brs2-brs5)
theorem stores_index_cases_def_complete (a0 : Int → Int) (n : Nat) (c : Int)
                                     (d : Int) (P : Int → Prop) :
  trace
    a0
    (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
    (fun a ⟨k, i⟩ =>
       if P k then
         fun j => if j = k then c else a j
       else
         fun j => if j = k then d else a j)
    = stores
      a0
      (butlast (counter 0 1 n))
      (maps (butlast (counter 0 1 n)) (fun k => if P k then c else d)) :=
  by
    have := stores_counter_read a0 (fun k _ => if P k then c else d) n 0 a0 (fun _ _ => rfl)
    simp only at this
    rw [← this]
    congr 1
    funext a p
    obtain ⟨k, i⟩ := p
    funext j
    by_cases h : P k <;> simp [h]

-- the former statement over the counter twice (trace_zip_self)
theorem stores_index_cases_zip :
  ∀ (a0 : Int → Int) (n : Nat) (c : Int) (d : Int) (P : Int → Prop),
    trace
      a0
      (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
      (fun a ⟨k, i⟩ =>
         if P k then
           fun j => if j = k then c else a j
         else
           if ¬P k then fun j => if j = k then d else a j else unspecified)
      = stores
        a0
        (butlast (counter 0 1 n))
        (maps (butlast (counter 0 1 n)) (fun k => if P k then c else d)) := by
  intro a0 n c d P
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact stores_index_cases_def_complete a0 n c d P

theorem stores_index_cases : Stmt.stores_index_cases := by
  intro a0 n c d P
  have h := stores_index_cases_zip a0 n c d P
  rw [trace_zip_self] at h
  exact h






-- on booleans, the guards are the values themselves; the occurrences of false come first,
-- since the guard b of the other lemma also matches !b, which counts the occurrences of true among the negations
theorem counts_false_def_complete (x : Int) (bs : List Prop) (n : Nat)
                               (hbs : length bs = n) :
  trace x bs (fun y b => if ¬b then y + 1 else y) = counts x False bs :=
  by
    simp only [counts]
    congr 1
    funext y b
    by_cases h : b <;> simp [h]

theorem counts_false : Stmt.counts_false := by
  intro x bs n hbs
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact counts_false_def_complete x bs n hbs

theorem counts_true_def_complete (x : Int) (bs : List Prop) (n : Nat)
                              (hbs : length bs = n) :
  trace x bs (fun y b => if b then y + 1 else y) = counts x True bs :=
  by
    simp only [counts]
    congr 1
    funext y b
    by_cases h : b <;> simp [h]

theorem counts_true : Stmt.counts_true := by
  intro x bs n hbs
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact counts_true_def_complete x bs n hbs

-- two cases whose results agree under the guard of the second one, x == c, which the simplifier has substituted
-- into it, are one; the second result is a variable d, since F(c) would be compared literally
-- (from copysome1-1, copysome1-2)
theorem trace_merge_cases_ne_complete (x0 : Int) (n : Nat) (c : Int) (d : Int)
                                   (F : Int → Int) :
  d = F c
    → trace x0 (butlast (counter 0 1 n)) (fun x k => if x ≠ c then F x else d)
      = trace x0 (butlast (counter 0 1 n)) (fun x k => F x) :=
  by
    intro h
    congr 1
    funext x k
    by_cases e : x = c <;> simp [e, h]

theorem trace_merge_cases_ne : Stmt.trace_merge_cases_ne := by
  intro x0 n c d F
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact trace_merge_cases_ne_complete x0 n c d F

-- stores at the positions 0, ..., n - 1 of values read from the array itself outside of that range read the initial
-- array
-- (from standard_palindrome_ground)
theorem stores_read_unmodified (a0 : Int → Int) (n : Nat)
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
      simpa using g n 0 a0 hs (fun _ _ => rfl) (by rw [integer_cast]; omega) hinv
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

theorem maps_identity {α : Type} [Inhabited α] (xs : List α) (n : Nat)
                                                     (hxs : length xs = n) :
  maps xs (fun x => x) = xs :=
  by
    induction xs generalizing n with
    | nil => rfl
    | cons x xs ih => simp only [maps]; rw [ih xs.length rfl]

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


-- auxiliary lemmas for the lemmas that hold for dependencies of equal length only (see bugs.md): the lengths of zipped
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
      simp only [butlast_counter_succ, invs, ih, integer_cast]
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
    rw [invs_counter_forall, integer_cast]
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
      simp only [butlast_counter_succ, invs, ih, integer_cast]
      cases m with
      | zero => (simp) <;> omega
      | succ m' =>
        have := step_mul (m' + 1) c (by omega)
        simp only [Nat.succ_ne_zero, false_or]
        push_cast at *
        constructor
        · intro ⟨h1, h2, h3⟩; constructor <;> grind
        · intro ⟨h1, h2⟩; refine ⟨h1, ?_, ?_⟩ <;> grind

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
theorem agree_prefix_def : Stmt.agree_prefix_def := by
  intro n xs ys _ _
  rw [agree_prefix_forall]
  refine (invs_counter_forall 0 n (fun k => earlier (natural k) xs = earlier (natural k) ys)).trans ?_
  simp [natural_eq]

-- a search: the elements before the exit n differ from e, i.e., e does not occur in the prefix of length n
-- (from standard_find_ground-1)
theorem not_occurs_prefix : Stmt.not_occurs_prefix := by
  intro n e xs hxs
  rw [not_occurs_prefix_forall n xs e hxs]
  refine (invs_counter_forall 0 n (fun k => earlier (natural k) xs ≠ e)).trans ?_
  simp [natural_eq]


-- the same for reads of an array at the positions of a counter: x does not occur among the values read there
-- (from lsearch)
theorem not_occurs_selects (a : Int → Int) (x : Int) (i : Int)
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
theorem above_iterations_def (n : Nat) (ts : List Int) (hts : length ts = n) :
  invs (List.zip (butlast (counter 0 1 n)) ts) (fun ⟨k, t⟩ => k < t)
    ↔ above_iterations n ts :=
  by
    rw [above_iterations_forall]
    refine (invs_zip_counter 0 n ts hts (fun k t => k < t)).trans ?_
    simp [integer_cast]

-- a choice of a loop whose values are all determined by the iteration constraint is a constant list
theorem consts_choice {α : Type} [Inhabited α] (n : Nat) (xs : List α)
                                                     (c : α)
                                                     (hxs : length xs = n) :
  invs (List.zip (butlast (counter 0 1 n)) xs) (fun ⟨k, x⟩ => x = c)
    ↔ xs = butlast (consts n c) :=
  by
    suffices h : ∀ (s : Int) (xs : List α), xs.length = n →
        (invs (List.zip (butlast (counter s 1 n)) xs) (fun ⟨k, x⟩ => x = c) ↔ xs = butlast (consts n c)) from
      h 0 xs hxs
    clear xs hxs
    induction n with
    | zero =>
      intro s xs h
      cases xs with
      | nil => simp [counter, butlast, invs, consts]
      | cons x xs => simp at h
    | succ m ih =>
      intro s xs h
      cases xs with
      | nil => simp at h
      | cons x xs =>
        rw [butlast_counter_succ, List.zip_cons_cons]
        simp only [invs, consts, butlast, List.cons.injEq]
        rw [ih (s + 1) xs (by simp at h; omega)]

-- butlast

-- a trace of n steps has n values before its last one, hence none if and only if n is zero
-- (from flag_loopdep)
theorem butlast_counter_nil (i : Int) (c : Int) (n : Nat) :
  butlast (counter i c n) = nil ↔ n = zero :=
  by cases n <;> simp [counter, butlast]

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

-- a histogram: the increments at the keys a[k] add to each cell v the number of occurrences of v among the keys, over
-- a counter from any start s
theorem current_trace_histogram_from (a : Int → Int) (v : Int) : ∀ (n : Nat) (s : Int) (c0 : Int → Int) (hs : List Int),
    hs.length = n →
    current (trace c0 (List.zip (butlast (counter s 1 n)) hs)
      (fun c ⟨k, h⟩ => fun j => if j = a k then c (a k) + 1 else c j)) v
      = c0 v + count v (selects a (butlast (counter s 1 n))) := by
  intro n
  induction n with
  | zero => intro s c0 hs _; simp [counter, butlast, trace, current, selects, maps, count]
  | succ n ih =>
    intro s c0 hs hl
    cases hs with
    | nil => simp at hl
    | cons h hs =>
      rw [butlast_counter_succ, List.zip_cons_cons]
      simp only [trace, current]
      rw [ih (s + 1) _ hs (by simpa using hl)]
      simp only [selects, maps, count]
      by_cases e : a s = v <;> simp [e] <;> omega

theorem current_trace_histogram : Stmt.current_trace_histogram := by
  intro c0 a n hs v hhs
  exact current_trace_histogram_from a v n 0 c0 hs hhs

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
theorem current_trace_two_phases_complete (x0 : Int) (n : Nat) (b : Int)
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
    rw [integer_cast]
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

theorem current_trace_two_phases : Stmt.current_trace_two_phases := by
  intro x0 n b c
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact current_trace_two_phases_complete x0 n b c

-- a follower: y increases by 1 whenever it does not exceed the value x of a counter with step 1, hence y is the
-- larger of its initial value and the final value of x, given that it starts at least at x
-- (from benchmark05_conjunctive)
theorem current_trace_catch_up_complete (y0 : Int) (x0 : Int) (n : Nat) :
  x0 ≤ y0
    → current
      (trace
         y0
         (List.zip (butlast (counter 0 1 n)) (butlast (counter x0 1 n)))
         (fun y ⟨k, x⟩ => if y ≤ x then y + 1 else y))
      = (if x0 + integer n ≤ y0 then y0 else x0 + integer n) :=
  by
    intro h
    rw [integer_cast]
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

theorem current_trace_catch_up : Stmt.current_trace_catch_up := by
  intro y0 x0 n
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact current_trace_catch_up_complete y0 x0 n

-- a flag, initially x0, that is set to c whenever D holds, is x0 at the end iff D never held, otherwise c, of any type
-- (from standard_compare_ground; examples/dafny/algorithms/is_sorted.dfy)
theorem current_trace_flag_complete {α : Type} [Inhabited α] (x0 : α) (c : α) (n : Nat) (hs : List Int)
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

theorem current_trace_flag : Stmt.current_trace_flag := by
  intro α _ x0 c n hs D hhs
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact current_trace_flag_complete x0 c n hs D hhs

-- the cell j of a trace that writes only j, setting it to c in the first iteration and adding G(k) in the others
-- (from MonoCera: brs1-brs5, ms2-ms5)
theorem select_current_trace_reset_add_complete (a0 : Int → Int) (j : Int)
                                             (n : Nat) (c : Int)
                                             (G : Int → Int) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
       (fun a ⟨k, i⟩ =>
          if k = 0 then
            fun j1 => if j1 = j then c else a j1
          else
            fun j1 => if j1 = j then a j + G k else a j1))
    j
    = (if n = zero then
         a0 j
       else
         c
           + sum
             (maps
                (butlast (counter 0 1 n))
                (fun k => if 0 < k then G k else 0))) :=
  by
    have later : ∀ (s : Int) (x : Int → Int) (m : Nat), 1 ≤ s →
        current (trace x (List.zip (butlast (counter s 1 m)) (butlast (counter s 1 m)))
          (fun a ⟨k, i⟩ => if k = 0 then fun j1 => if j1 = j then c else a j1
            else fun j1 => if j1 = j then a j + G k else a j1)) j
        = x j + sum (maps (butlast (counter s 1 m)) G) := by
      intro s x m hs
      induction m generalizing s x with
      | zero => simp [counter, butlast, trace, current, maps, sum]
      | succ t ih =>
        simp only [butlast_counter_succ, List.zip_cons_cons, trace, current, maps, sum]
        rw [ite_eq_right_iff.mpr (by omega), ih (s + 1) _ (by omega)]
        simp only [ite_true]
        omega
    cases n with
    | zero => simp [counter, butlast, trace, current]
    | succ m =>
      have h := later 1 (fun j1 => if j1 = j then c else a0 j1) m (by omega)
      have e : maps (butlast (counter 1 1 m)) (fun k => if 0 < k then G k else 0) = maps (butlast (counter 1 1 m)) (fun k => G k) :=
        maps_counter_congr 1 m _ _ (fun k hk => by simp [show 0 < k by omega])
      rw [sum_counter_succ]
      simp only [butlast_counter_succ, List.zip_cons_cons, trace, current, Int.zero_add] at h e ⊢
      simp only [ite_true, Nat.succ_ne_zero, ite_false] at h ⊢
      rw [h, e]
      simp

-- the former statement over the counter twice (trace_zip_self)
theorem select_current_trace_reset_add_zip :
  ∀ (a0 : Int → Int) (j : Int) (n : Nat) (c : Int) (G : Int → Int),
    current
      (trace
         a0
         (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
         (fun a ⟨k, i⟩ =>
            if k = 0 then
              fun j1 => if j1 = j then c else a j1
            else
              if 0 < k then
                fun j1 => if j1 = j then a j + G k else a j1
              else
                unspecified))
      j
      = (if n = zero then
           a0 j
         else
           c
             + sum
               (maps
                  (butlast (counter 0 1 n))
                  (fun k => if 0 < k then G k else 0))) := by
  intro a0 j n c G
  rw [trace_counter_congr a0 0 n _ _
    (fun a ⟨k, i⟩ => if k = 0 then fun j1 => if j1 = j then c else a j1 else fun j1 => if j1 = j then a j + G k else a j1)
    (fun a k y h1 h2 => by
      dsimp only; by_cases e : k = 0 <;> simp only [e, ↓reduceIte]; rw [if_pos (show 0 < k by omega)])]
  exact select_current_trace_reset_add_complete a0 j n c G

theorem select_current_trace_reset_add : Stmt.select_current_trace_reset_add := by
  intro a0 j n c G
  have h := select_current_trace_reset_add_zip a0 j n c G
  rw [trace_zip_self] at h
  exact h

-- the same where the other iterations keep the array
-- (from MonoCera: ms1)
theorem select_current_trace_reset_keep_complete (a0 : Int → Int) (j : Int)
                                              (n : Nat) (c : Int) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
       (fun a ⟨k, i⟩ =>
          if k = 0 then fun j1 => if j1 = j then c else a j1 else a))
    j
    = (if n = zero then a0 j else c) :=
  by
    have later : ∀ (s : Int) (x : Int → Int) (m : Nat), 1 ≤ s →
        current (trace x (List.zip (butlast (counter s 1 m)) (butlast (counter s 1 m)))
          (fun a ⟨k, i⟩ => if k = 0 then fun j1 => if j1 = j then c else a j1 else a)) = x := by
      intro s x m hs
      induction m generalizing s x with
      | zero => simp [counter, butlast, trace, current]
      | succ t ih =>
        simp only [butlast_counter_succ, List.zip_cons_cons, trace, current]
        simp only [show ¬ (s = 0) by omega, ite_false]
        rw [ih (s + 1) _ (by omega)]
    cases n with
    | zero => simp [counter, butlast, trace, current]
    | succ m =>
      have h := later 1 (fun j1 => if j1 = j then c else a0 j1) m (by omega)
      simp only [butlast_counter_succ, List.zip_cons_cons, trace, current, Int.zero_add] at h ⊢
      simp only [ite_true, Nat.succ_ne_zero, ite_false]
      rw [h]
      simp

-- the former statement over the counter twice (trace_zip_self)
theorem select_current_trace_reset_keep_zip :
  ∀ (a0 : Int → Int) (j : Int) (n : Nat) (c : Int),
    current
      (trace
         a0
         (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
         (fun a ⟨k, i⟩ =>
            if k = 0 then
              fun j1 => if j1 = j then c else a j1
            else
              if 0 < k then a else unspecified))
      j
      = (if n = zero then a0 j else c) := by
  intro a0 j n c
  rw [trace_counter_congr a0 0 n _ _
    (fun a ⟨k, i⟩ => if k = 0 then fun j1 => if j1 = j then c else a j1 else a)
    (fun a k y h1 h2 => by
      dsimp only; by_cases e : k = 0 <;> simp only [e, ↓reduceIte]; rw [if_pos (show 0 < k by omega)])]
  exact select_current_trace_reset_keep_complete a0 j n c

theorem select_current_trace_reset_keep : Stmt.select_current_trace_reset_keep := by
  intro a0 j n c
  have h := select_current_trace_reset_keep_zip a0 j n c
  rw [trace_zip_self] at h
  exact h

-- earlier

theorem earlier_counter (k : Nat) (i : Int) (c : Int) (n : Nat) :
  integer k < integer n → earlier k (butlast (counter i c n)) = i + integer k * c :=
  by
    intro h
    induction n generalizing i k with
    | zero => simp only [integer_cast] at h; omega
    | succ m ih =>
      cases k with
      | zero => simp [butlast_counter_succ, earlier, integer]
      | succ j =>
        have h' : integer j < integer m := by simp only [integer_cast] at h ⊢; omega
        simp [butlast_counter_succ, earlier, ih j (i + c) h', integer]; grind

theorem earlier_consts {α : Type} [Inhabited α] (k : Nat) (n : Nat)
                                                      (x : α) :
  integer k < integer n → earlier k (butlast (consts n x)) = x :=
  by
    intro h
    induction n generalizing k with
    | zero => simp only [integer_cast] at h; omega
    | succ m ih =>
      cases k with
      | zero => simp [consts, butlast, earlier]
      | succ j =>
        have h' : integer j < integer m := by simp only [integer_cast] at h ⊢; omega
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
    | nil => rw [← hkeys] at h; simp only [integer_cast, List.length_nil] at h; omega
    | cons k ks ih =>
      cases j with
      | zero => simp [selects, maps, earlier]
      | succ i =>
        simp only [selects, maps, earlier]
        exact ih i ks.length rfl (by simp at hkeys; simp only [integer_cast] at h ⊢; omega)

theorem earlier_sums (j : Nat) (x : Int) (values : List Int) (n : Nat)
                           (hvalues : length values = n) :
  integer j < integer n → earlier j (butlast (sums x values)) = x + sum («prefix» j values) :=
  by
    intro h
    induction values generalizing j x n with
    | nil => rw [← hvalues] at h; simp only [integer_cast, List.length_nil] at h; omega
    | cons v vs ih =>
      have e : sums x (v :: vs) = .step x (sums (x + v) vs) := rfl
      rw [e]
      cases j with
      | zero => simp [butlast, earlier, «prefix», sum]
      | succ i =>
        simp only [butlast, earlier, «prefix», sum]
        rw [ih i (x + v) vs.length rfl (by simp at hvalues; simp only [integer_cast] at h ⊢; omega)]
        omega

theorem earlier_counts {α : Type} [Inhabited α] (j : Nat) (x : Int)
                                                      (e : α) (vs : List α)
                                                      (n : Nat)
                                                      (hvs : length vs = n) :
  integer j < integer n → earlier j (butlast (counts x e vs)) = x + count e («prefix» j vs) :=
  by
    intro h
    induction vs generalizing j x n with
    | nil => rw [← hvs] at h; simp only [integer_cast, List.length_nil] at h; omega
    | cons v vs ih =>
      have e' : counts x e (v :: vs) = .step x (counts (if v = e then x + 1 else x) e vs) := by
        simp only [counts, trace, ite_eq_ne]
      rw [e']
      cases j with
      | zero => simp [butlast, earlier, «prefix», count]
      | succ i =>
        simp only [butlast, earlier, «prefix», count]
        rw [ih i _ vs.length rfl (by simp at hvs; simp only [integer_cast] at h ⊢; omega)]
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
      | zero => simp only [integer_cast] at h; omega
      | succ m =>
        cases j with
        | zero => simp [«prefix», earlier]
        | succ i => simp only [«prefix», earlier]; exact ih i m (by simp only [integer_cast] at h ⊢; omega)

-- agreeing sequences are equal at each position in the range; the atom is the left-hand side
-- (from standard_compare_ground)
theorem earlier_agree_prefix (n : Nat) (j : Nat) (xs : List Int)
                                   (ys : List Int) :
  agree_prefix n xs ys ∧ integer j < integer n
    → earlier j xs = earlier j ys :=
  by
    intro ⟨h, hj⟩
    simp only [integer_cast] at hj
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
  ¬occurs e («prefix» n xs) ∧ integer j < integer n → earlier j xs ≠ e :=
  by
    intro ⟨h1, h2⟩
    rw [not_occurs_prefix_forall n xs e hxs] at h1
    simp only [integer_cast] at h2
    exact h1 j (by omega)

-- the same for reads of an array, at the positions k of the counter
-- (from lsearch)
theorem select_not_occurs_selects (a : Int → Int) (x : Int) (i : Int)
                                        (n : Nat) (k : Int) :
  ¬occurs x (selects a (butlast (counter i 1 n))) ∧ i ≤ k ∧ k < i + integer n
    → a k ≠ x :=
  by
    intro ⟨h, h1, h2⟩
    intro e
    apply h
    rw [integer_cast] at h2
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
    · exact (select_not_occurs_selects a x 0 n j ⟨h, hj, by omega⟩ e).elim
    · exact hle

-- the sentinel x stored at j occurs among the values read at 0, ..., n - 1 unless j is beyond them
theorem store_occurs_selects (n : Nat) (j : Int) (x : Int) (a : Int → Int) :
  0 ≤ j → occurs x (selects (fun j1 => if j1 = j then x else a j1) (butlast (counter 0 1 n))) ∨ integer n ≤ j :=
  by
    intro hj
    by_cases h : occurs x (selects (fun j1 => if j1 = j then x else a j1) (butlast (counter 0 1 n)))
    · exact Or.inl h
    · exact Or.inr (select_not_occurs_selects_beyond n j x _ ⟨h, by simp, hj⟩)

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
      | succ j => simp only [integer_cast] at h; omega
    | succ m ih => cases k with
      | zero => rfl
      | succ j =>
        simp only [butlast_counter_succ, «prefix»]
        rw [ih j (i + c) (by simp only [integer_cast] at h ⊢; omega)]

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
      | succ j => simp only [integer_cast] at h; omega
    | succ m ih =>
      cases ys with
      | nil => simp at hys
      | cons y ys => cases k with
        | zero => rfl
        | succ j =>
          simp only [butlast_counter_succ, List.zip_cons_cons, maps, «prefix»]
          rw [ih j (i + c) ys (by simpa using hys) (by simp only [integer_cast] at h ⊢; omega)]

theorem prefix_sums (k : Nat) (x : Int) (values : List Int) (n : Nat)
                          (hvalues : length values = n) :
  «prefix» k (butlast (sums x values)) = butlast (sums x («prefix» k values)) :=
  by simp only [sums]; exact prefix_butlast_trace k x values _

-- occurs

theorem occurs_counter_up (j : Int) (i : Int) (n : Nat) :
  occurs j (butlast (counter i 1 n)) ↔ i ≤ j ∧ j < i + integer n :=
  by
    induction n generalizing i with
    | zero => (simp [counter, butlast, occurs, integer]) <;> omega
    | succ m ih => simp only [butlast_counter_succ, occurs, ih, integer_cast]; omega

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
      simp only [butlast_counter_succ, occurs, ih, integer_cast]
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

-- the value i + d q of a counter with a positive step d is at position q, by induction over the steps
theorem indexof_counter_step_mul (d : Int) (hd : 0 < d) :
    ∀ (n : Nat) (i : Int) (q : Nat), q < n → indexof (i + d * q) (butlast (counter i d n)) = q := by
  intro n
  induction n with
  | zero => intro i q h; omega
  | succ m ih =>
    intro i q hq
    rw [butlast_counter_succ, indexof]
    cases q with
    | zero =>
      have h : ¬ occurs (i + d * ((0 : Nat) : Int)) (butlast (counter (i + d) d m)) := by
        rw [occurs_counter_step (i + d) d m _ hd]; push_cast; omega
      rw [if_neg h]
    | succ q =>
      have e : i + d * ((q + 1 : Nat) : Int) = (i + d) + d * (q : Int) := by
        push_cast; rw [Int.mul_add, Int.mul_one]; omega
      have hq' : q < m := by omega
      have hm : d * (q : Int) < (m : Int) * d := by
        rw [Int.mul_comm (m : Int) d]; exact Int.mul_lt_mul_of_pos_left (by omega) hd
      have occ : occurs ((i + d) + d * (q : Int)) (butlast (counter (i + d) d m)) := by
        rw [occurs_counter_step (i + d) d m _ hd, integer_cast]
        refine ⟨?_, by omega, ?_⟩
        · have := Int.mul_nonneg (Int.le_of_lt hd) (Int.natCast_nonneg q); omega
        · rw [show (i + d) + d * (q : Int) - (i + d) = d * (q : Int) by omega]; exact Int.mul_emod_right d q
      rw [e, if_pos occ, ih (i + d) q hq']

theorem indexof_counter_step : Stmt.indexof_counter_step := by
  intro j i d n ⟨hd, h1, h2, h3⟩
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero h3
  rw [integer_cast] at h2
  have hc0 : 0 ≤ c := by
    rcases Int.lt_or_le c 0 with h | h
    · have := Int.mul_lt_mul_of_pos_left h hd; omega
    · exact h
  have hcn : c < (n : Int) := by
    rcases Int.lt_or_le c (n : Int) with h | h
    · exact h
    · have := Int.mul_le_mul_of_nonneg_left h (Int.le_of_lt hd); rw [Int.mul_comm d (n : Int)] at this; omega
  have hj : j = i + d * ((c.toNat : Nat) : Int) := by rw [Int.toNat_of_nonneg hc0]; omega
  rw [hj, indexof_counter_step_mul d hd n i c.toNat (by omega), natural_eq]
  rw [show i + d * ((c.toNat : Nat) : Int) - i = d * ((c.toNat : Nat) : Int) by omega,
      Int.mul_ediv_cancel_left _ (by omega : d ≠ 0)]
  simp [Int.max_eq_left hc0]

-- no keys select no values
theorem selects_nil : Stmt.selects_nil := by
  intro α β _ _ a; rfl

-- indexof

theorem indexof_counter_up (j : Int) (i : Int) (n : Nat) :
  i ≤ j ∧ j < i + integer n
    → indexof j (butlast (counter i 1 n)) = natural (j - i) :=
  by
    intro ⟨h1, h2⟩
    rw [integer_cast] at h2
    induction n generalizing i with
    | zero => (simp at h2) <;> omega
    | succ m ih =>
      rw [butlast_counter_succ, indexof]
      have hocc : occurs j (butlast (counter (i + 1) 1 m)) ↔ i + 1 ≤ j := by
        rw [occurs_counter_up, integer_cast]; push_cast at h2; omega
      by_cases e : i + 1 ≤ j
      · rw [ite_eq_left (hocc.mpr e), ih (i + 1) e (by push_cast at h2; omega), natural_eq, natural_eq]
        show (j - (i + 1)).toNat + 1 = (j - i).toNat
        omega
      · rw [ite_eq_right (fun h => e (hocc.mp h)), natural_eq]
        show (0 : Nat) = (j - i).toNat
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
    simp only [integer_cast] at h
    have hlen : (List.zip keys values).length = n := length_zip_eq keys values n hkeys hvalues
    rw [stores, earlier_butlast_trace j a (List.zip keys values) _ (by omega), prefix_zip, ← stores,
        current_stores k a («prefix» j keys) («prefix» j values) j (length_prefix j keys (by omega))
          (length_prefix j values (by omega))]
    by_cases ho : occurs k («prefix» j keys)
    · simp only [ho, ite_true]
      have hi := indexof_lt_length k _ ho
      rw [length_prefix j keys (by omega)] at hi
      rw [earlier_prefix _ j values (by simp only [integer_cast]; omega)]
    · simp only [ho, ite_false]

-- stores at the positions of a counter, guarded by C, keep the other positions; a read at j
-- (from copysome1-1, copysome1-2)
theorem current_trace_conditional_store_complete (a0 : Int → Int) (n : Nat)
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
    rw [integer_cast]
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

-- the former statement over the counter twice (trace_zip_self)
theorem select_current_trace_conditional_store_zip :
  ∀ (a0 : Int → Int) (n : Nat) (j : Int) (C : Int → Prop) (V : Int → Int),
    current
      (trace
         a0
         (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
         (fun a ⟨k, i⟩ =>
            if C i then
              fun j => if j = i then V i else a j
            else
              if ¬C i then a else unspecified))
      j
      = (if 0 ≤ j ∧ j < integer n ∧ C j then V j else a0 j) := by
  intro a0 n j C V
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact current_trace_conditional_store_complete a0 n j C V

theorem select_current_trace_conditional_store : Stmt.select_current_trace_conditional_store := by
  intro a0 n j C V
  have h := select_current_trace_conditional_store_zip a0 n j C V
  rw [trace_zip_self] at h
  exact h

-- the same, with the guard and the value on the values of three further dependencies at the iteration of j
-- (from array_mul_init)
theorem current_trace_conditional_store_deps_complete (a0 : Int → Int) (n : Nat)
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
    rw [integer_cast]
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

theorem select_current_trace_conditional_store_deps : Stmt.select_current_trace_conditional_store_deps := by
  intro a0 n j hs cs vs C V hhs hcs hvs
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact current_trace_conditional_store_deps_complete a0 n j hs cs vs C V hhs hcs hvs

-- a clamp of each element to b, where the guard reads the initial element, since each position is written in its own
-- iteration only; a generic guard C(a[k], k) is no pattern, and C(a, k) would read other positions
-- (from condn, condnf)
theorem current_trace_cap_complete (a0 : Int → Int) (n : Nat) (j : Int) (b : Int) :
  current
    (trace
       a0
       (butlast (counter 0 1 n))
       (fun a k =>
          if a k < b then a else fun j => if j = k then b else a j))
    j
    = (if 0 ≤ j ∧ j < integer n ∧ b ≤ a0 j then b else a0 j) :=
  by
    rw [integer_cast]
    -- from position s on, where the positions from s on still hold their initial values
    have gen : ∀ (m : Nat) (s : Int) (a : Int → Int), (∀ x, s ≤ x → a x = a0 x) →
        current (trace a (butlast (counter s 1 m))
          (fun a k => if a k < b then a else fun j => if j = k then b else a j)) j
        = (if s ≤ j ∧ j < s + m ∧ b ≤ a0 j then b else a j) := by
      intro m
      induction m with
      | zero =>
        intro s a ha
        simp only [counter, butlast, trace, current]
        exact (ite_eq_right (by intro ⟨_, h', _⟩; simp at h'; omega)).symm
      | succ t ih =>
        intro s a ha
        rw [butlast_counter_succ]
        simp only [trace, current]
        rw [ih (s + 1) _
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
    have := gen n 0 a0 (fun _ _ => rfl)
    simpa using this

theorem select_current_trace_cap : Stmt.select_current_trace_cap := by
  intro a0 n j b
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact current_trace_cap_complete a0 n j b

-- an array filled by a recurrence at the positions 1, ..., n, each element from its predecessor plus G of the position
-- of the predecessor, is the initial element plus the sum of G over the positions before
-- (from eqn1, eqn1f, nsqm, nsqmf, pcomp, pcompf, sqm)
theorem select_current_trace_prefix_sums (b0 : Int → Int) (n : Nat) (j : Int)
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
    rw [integer_cast, natural_eq]
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
theorem select_current_trace_prefix_sums_add (b0 : Int → Int) (n : Nat) (j : Int)
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
    rw [integer_cast, natural_eq]
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

-- sum, which is linear, and the linear transformations are moved to the outside

theorem sum_empty : sum nil = 0 :=
  by rfl

theorem sum_consts (n : Nat) (x : Int) :
  sum (butlast (consts n x)) = x * integer n :=
  by
    induction n with
    | zero => simp [consts, butlast, sum, integer]
    | succ m ih => simp [consts, butlast, sum, ih, integer]; grind

-- a sum of n terms that are each 0, c, or d is at most n times the largest of them
-- (from MonoCera: brs2-brs5)
theorem sum_cases_below (n : Nat) (c : Int) (d : Int) (e : Int)
                              (P : Int → Prop) :
  0 ≤ e ∧ integer n * c ≤ e ∧ integer n * d ≤ e
    → sum
      (maps
         (butlast (counter 0 1 n))
         (fun k => if 0 < k then if P k then c else d else 0))
      ≤ e :=
  by
    intro ⟨he, hc, hd⟩
    rw [integer_cast] at hc hd
    by_cases h1 : d ≤ c ∧ 0 ≤ c
    · refine Int.le_trans (sum_counter_le 0 n _ c ?_) hc
      intro k _ _; (repeat' split) <;> omega
    · by_cases h2 : c ≤ d ∧ 0 ≤ d
      · refine Int.le_trans (sum_counter_le 0 n _ d ?_) hd
        intro k _ _; (repeat' split) <;> omega
      · have := sum_counter_le 0 n (fun k => if 0 < k then if P k then c else d else 0) 0
          (by intro k _ _; (repeat' split) <;> omega)
        omega

-- a sum of n remainders k % m of the iterations k from 0 is at most n (m - 1)
-- (from MonoCera: ms2-ms5)
theorem sum_mod_below (n : Nat) (m : Int) (e : Int) :
  0 < m ∧ integer n * (m - 1) ≤ e
    → sum (maps (butlast (counter 0 1 n)) (fun k => if 0 < k then k % m else 0))
      ≤ e :=
  by
    intro ⟨hm, he⟩
    rw [integer_cast] at he
    refine Int.le_trans (sum_counter_le 0 n _ (m - 1) ?_) he
    intro k hk _
    have := Int.emod_lt_of_pos k hm
    have := Int.emod_nonneg k (show m ≠ 0 by omega)
    split <;> omega

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
      | succ m ih => simp only [butlast_counter_succ, sum, integer_cast] at *; push_cast; grind
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

-- parity

-- count

theorem count_consts {α : Type} [Inhabited α] (n : Nat) (e : α) (v : α) :
  count e (butlast (consts n v)) = (if v = e then integer n else 0) :=
  by
    induction n with
    | zero => simp [consts, butlast, count, integer]
    | succ m ih => simp only [consts, butlast, count, ih, integer]; split <;> omega

-- the iterations of a counter by 1 before m and from m on, e.g. for loops with if (i < m) in the body
theorem count_true_below (m : Int) (i : Int) (n : Nat) :
  i ≤ m ∧ m ≤ i + integer n
    → count True (maps (butlast (counter i 1 n)) (fun k => k < m)) = m - i :=
  by intro ⟨h1, h2⟩; rw [(count_lt_counter m i n).1]; simp only [integer_cast] at *; omega

theorem count_true_above (m : Int) (i : Int) (n : Nat) :
  i ≤ m ∧ m ≤ i + integer n
    → count True (maps (butlast (counter i 1 n)) (fun k => m ≤ k))
      = i + integer n - m :=
  by intro ⟨h1, h2⟩; rw [(count_le_counter m i n).1]; simp only [integer_cast] at *; omega

theorem count_nonnegative {α : Type} [Inhabited α] (e : α) (vs : List α) :
  0 ≤ count e vs :=
  by
    induction vs with
    | nil => simp [count]
    | cons v ws ih => simp only [count]; split <;> omega

-- the numbers 0, ..., n - 1 with the remainder r modulo m number (n + m - 1 - r) / m
-- (from half, sumt2)
theorem count_remainder : Stmt.count_remainder := by
    intro n m r ⟨hm, hr0, hrm⟩
    rw [integer_cast]
    have hr : r % m = r := Int.emod_eq_of_lt hr0 hrm
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
    rw [integer_cast, ← hlen]
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
      simp only [maxs, trace, current, ite_lt_le] at *
      have h1 := ih (if x < v then v else x)
      have h2 : x ≤ (if x < v then v else x) := by split <;> omega
      omega

theorem current_maxs_earlier (k : Nat) (x : Int) (values : List Int)
                                   (n : Nat) (hvalues : length values = n) :
  integer k < integer n → earlier k values ≤ current (maxs x values) :=
  by
    intro h
    induction values generalizing k x n with
    | nil => rw [← hvalues] at h; simp only [integer_cast, List.length_nil] at h; omega
    | cons v vs ih =>
      have e : maxs x (v :: vs) = .step x (maxs (if x < v then v else x) vs) := by
        simp only [maxs, trace, ite_lt_le]
      rw [e]
      simp only [current]
      cases k with
      | zero =>
        simp only [earlier]
        have := current_maxs_initial (if x < v then v else x) vs vs.length rfl
        by_cases hv : x < v <;> simp only [hv, ite_true, ite_false] at this ⊢ <;> omega
      | succ i =>
        simp only [earlier]
        exact ih i _ vs.length rfl (by simp at hvalues; simp only [integer_cast] at h ⊢; omega)

theorem current_mins_initial (x : Int) (values : List Int) (n : Nat)
                                   (hvalues : length values = n) :
  current (mins x values) ≤ x :=
  by
    clear hvalues n
    induction values generalizing x with
    | nil => simp [mins, trace, current]
    | cons v vs ih =>
      simp only [mins, trace, current, ite_lt_le] at *
      have h1 := ih (if v < x then v else x)
      have h2 : (if v < x then v else x) ≤ x := by split <;> omega
      omega

theorem current_mins_earlier (k : Nat) (x : Int) (values : List Int)
                                   (n : Nat) (hvalues : length values = n) :
  integer k < integer n → current (mins x values) ≤ earlier k values :=
  by
    intro h
    induction values generalizing k x n with
    | nil => rw [← hvalues] at h; simp only [integer_cast, List.length_nil] at h; omega
    | cons v vs ih =>
      have e : mins x (v :: vs) = .step x (mins (if v < x then v else x) vs) := by
        simp only [mins, trace, ite_lt_le]
      rw [e]
      simp only [current]
      cases k with
      | zero =>
        simp only [earlier]
        have := current_mins_initial (if v < x then v else x) vs vs.length rfl
        by_cases hv : v < x <;> simp only [hv, ite_true, ite_false] at this ⊢ <;> omega
      | succ i =>
        simp only [earlier]
        exact ih i _ vs.length rfl (by simp at hvalues; simp only [integer_cast] at h ⊢; omega)

-- a value that increases by a positive constant in each of its three cases exceeds its initial value after at
-- least one iteration
-- (from large_const)
theorem current_trace_increasing_complete (x0 : Int) (n : Nat) (a : Int) (b : Int)
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
              if C h then x + a else if D h then x + b else if E h then x + c else x + a)) :=
  by
    intro ⟨hn, ha, hb, hc⟩
    have hstrict : ∀ (x : Int) (p : Int × Int),
        x < (fun x (p : Int × Int) => match p with
          | (k, h) => if C h then x + a else if D h then x + b else if E h then x + c else x + a) x p := by
      intro x ⟨k, h⟩
      show x < (if C h then x + a else if D h then x + b else if E h then x + c else x + a)
      split
      · omega
      · split
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

theorem current_trace_increasing : Stmt.current_trace_increasing := by
  intro x0 n a b c hs C D E hhs
  -- the fourth case is the complement of the others, so the conditional never reaches unspecified
  have e : ∀ (h A B C' z : Int), (if C h then A else if D h then B else if E h then C' else if ¬(C h ∨ D h ∨ E h) then A else z)
      = (if C h then A else if D h then B else if E h then C' else A) := by
    intro h A B C' z
    by_cases h1 : C h <;> by_cases h2 : D h <;> by_cases h3 : E h <;> simp [h1, h2, h3]
  simp only [e]
  exact current_trace_increasing_complete x0 n a b c hs C D E hhs

-- an interval that contains the initial value and that each of the three cases maps into itself contains the
-- current value, an inductive invariant; the left-hand side is the conjunction of both bounds, which binds both
-- (from benchmark51_polynomial)
theorem current_trace_bounded_complete (x0 : Int) (n : Nat) (lo : Int) (hi : Int)
                                    (C1 : Int → Prop) (C2 : Int → Prop)
                                    (C3 : Int → Prop) (F1 : Int → Int)
                                    (F2 : Int → Int) (F3 : Int → Int) :
  lo ≤ x0
    ∧ x0 ≤ hi
    ∧ (∀ (y : Int), lo ≤ y ∧ y ≤ hi ∧ C1 y → lo ≤ F1 y ∧ F1 y ≤ hi)
    ∧ (∀ (y : Int), lo ≤ y ∧ y ≤ hi ∧ C2 y → lo ≤ F2 y ∧ F2 y ≤ hi)
    ∧ (∀ (y : Int), lo ≤ y ∧ y ≤ hi ∧ C3 y → lo ≤ F3 y ∧ F3 y ≤ hi)
    → (lo
         ≤ current
           (trace
              x0
              (butlast (counter 0 1 n))
              (fun x k => if C1 x then F1 x else if C2 x then F2 x else if C3 x then F3 x else x))
         ∧ current
           (trace
              x0
              (butlast (counter 0 1 n))
              (fun x k => if C1 x then F1 x else if C2 x then F2 x else if C3 x then F3 x else x))
           ≤ hi
         ↔ True) :=
  by
    intro ⟨h1, h2, f1, f2, f3⟩
    simp only [iff_true]
    suffices g : ∀ s x, lo ≤ x ∧ x ≤ hi → lo ≤ current (trace x (butlast (counter s 1 n))
        (fun x k => if C1 x then F1 x else if C2 x then F2 x else if C3 x then F3 x else x)) ∧ current (trace x (butlast (counter s 1 n))
        (fun x k => if C1 x then F1 x else if C2 x then F2 x else if C3 x then F3 x else x)) ≤ hi from g 0 x0 ⟨h1, h2⟩
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
        · rw [ite_eq_right c2]
          by_cases c3 : C3 x
          · rw [ite_eq_left c3]; exact f3 x ⟨hx.1, hx.2, c3⟩
          · rw [ite_eq_right c3]; exact hx

theorem current_trace_bounded : Stmt.current_trace_bounded := by
  intro x0 n lo hi C1 C2 C3 F1 F2 F3
  -- the fourth case is the complement of the others, so the conditional never reaches unspecified
  have e : ∀ (y A B C z : Int), (if C1 y then A else if C2 y then B else if C3 y then C else if ¬(C1 y ∨ C2 y ∨ C3 y) then y else z)
      = (if C1 y then A else if C2 y then B else if C3 y then C else y) := by
    intro y A B C z
    by_cases h1 : C1 y <;> by_cases h2 : C2 y <;> by_cases h3 : C3 y <;> simp [h1, h2, h3]
  simp only [e]
  exact current_trace_bounded_complete x0 n lo hi C1 C2 C3 F1 F2 F3

-- which is instantiated at the positions j in the range
-- (from simple_array_index_value_2)
theorem earlier_above_iterations (n : Nat) (j : Nat) (ts : List Int) :
  above_iterations n ts ∧ integer j < integer n
    → integer j < earlier j ts :=
  by
    intro ⟨h, hj⟩
    simp only [integer_cast] at hj
    induction n with
    | zero => omega
    | succ m ih =>
      simp only [above_iterations] at h
      by_cases e : j = m
      · subst e; simpa [integer_cast] using h.2
      · exact ih h.1 (by omega)

-- arithmetic, in the normal form of the simplifier

-- a positive number divides itself
-- (from modn, modnf)
theorem mod_self (x : Int) : 0 < x → x % x = 0 :=
  by intro h; exact Int.emod_self

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

theorem triangle_nonneg (x : Int) : 0 ≤ (x + x * x) / 2 :=
  by
    have h : 0 ≤ x * (x + 1) := by
      rcases Int.lt_or_le x 0 with h | h
      · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · exact Int.mul_nonneg h (by omega)
    have e : x * (x + 1) = x + x * x := by grind
    omega

-- x + x * x and -x + x * x are even, by the parity of x
theorem triangle_even (x : Int) : 2 * ((x + x * x) / 2) = x + x * x :=
  by
    have h : (x + x * x) % 2 = 0 := by
      rw [Int.add_emod, Int.mul_emod]
      have : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases this with e | e <;> simp [e]
    omega

-- -x + x * x is x + x * x less 2 * x
theorem triangle_even_below (x : Int) : 2 * ((-x + x * x) / 2) = -x + x * x :=
  by have := triangle_even x; omega

theorem triangle_nonneg_below (x : Int) : 0 ≤ (-x + x * x) / 2 :=
  by
    have h : 0 ≤ x * (x - 1) := by
      rcases Int.lt_or_le x 1 with h | h
      · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · exact Int.mul_nonneg (by omega) (by omega)
    have e : x * (x - 1) = -x + x * x := by grind
    omega

theorem div_below (b : Int) (x : Int) (d : Int) :
  0 < d ∧ 0 ≤ x ∧ x < d * (b + 1) → (b < x / d ↔ False) :=
  by
    intro ⟨hd, _, hx⟩
    have : x / d < b + 1 := Int.ediv_lt_of_lt_mul hd (by rw [Int.mul_comm] at hx; exact hx)
    simp only [iff_false]
    omega

-- the quotient of a positive divisor is not positive exactly below it
-- (from MonoCera: pr2)
theorem div_nonpos (x : Int) (c : Int) : 0 < c → (x / c ≤ 0 ↔ x < c) :=
  by
    intro hc
    rw [show (x / c ≤ 0) ↔ (x / c < 1) by omega, Int.ediv_lt_iff_lt_mul hc, Int.one_mul]

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
theorem invs_two_phases_complete (x0 : Int) (n : Nat) (b : Int) (c : Int)
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
          prefix_counter i 0 1 n (by simp only [integer_cast]; omega)]
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
      have hlast := current_trace_two_phases_complete x0 t b c ⟨hx, Int.le_of_lt hc⟩
      have e : integer (t + 1) - 1 = integer t := by simp only [integer_cast]; push_cast; omega
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

theorem invs_two_phases : Stmt.invs_two_phases := by
  intro x0 n b c B
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact invs_two_phases_complete x0 n b c B

-- sorted.dfy: sorted, perm and partitioned as defined in the module

theorem sorted_empty (a : Int → Int) (lo : Int) : sorted a lo lo ↔ True := by
  simp only [sorted, iff_true]; intro i j ⟨h1, h2, h3⟩; omega

theorem sorted_short (a : Int → Int) (lo hi : Int) : hi ≤ lo + 1 → (sorted a lo hi ↔ True) := by
  intro h; simp only [sorted, iff_true]; intro i j ⟨h1, h2, h3⟩
  rw [show j = i by omega]; exact Int.le_refl _

theorem partitioned_empty (a : Int → Int) (lo hi : Int) : partitioned a lo lo hi ↔ True := by
  simp only [partitioned, iff_true]; intro i j ⟨h1, h2, h3, h4⟩; omega

theorem partitioned_whole (a : Int → Int) (lo hi : Int) : partitioned a lo hi hi ↔ True := by
  simp only [partitioned, iff_true]; intro i j ⟨h1, h2, h3, h4⟩; omega

theorem sorted_mono (a : Int → Int) (lo hi hi' : Int) : hi' ≤ hi → sorted a lo hi → sorted a lo hi' :=
  fun h hs i j ⟨h1, h2, h3⟩ => hs i j ⟨h1, h2, by omega⟩

-- adjacent pairs along two counters
theorem invs_adjacent (a : Int → Int) (s : Int) (n : Nat) :
    invs (List.zip (butlast (counter s 1 n)) (butlast (counter (s + 1) 1 n))) (fun ⟨k, i⟩ => a k ≤ a i)
      ↔ ∀ k, s ≤ k → k < s + n → a k ≤ a (k + 1) := by
  induction n generalizing s with
  | zero => simp [counter, butlast, invs]; intro k h1 h2; omega
  | succ m ih =>
    rw [butlast_counter_succ, butlast_counter_succ, List.zip_cons_cons]
    simp only [invs]; rw [ih (s + 1)]
    constructor
    · intro ⟨h, hs⟩ k h1 h2
      by_cases e : k = s
      · subst e; exact h
      · exact hs k (by omega) (by omega)
    · intro h; exact ⟨h s (by omega) (by omega), fun k h1 h2 => h k (by omega) (by omega)⟩

theorem sorted_adjacent (a : Int → Int) (n : Nat) :
    invs (List.zip (butlast (counter 0 1 n)) (butlast (counter 1 1 n))) (fun ⟨k, i⟩ => a k ≤ a i)
      ↔ sorted a 0 (integer n + 1) := by
  have := invs_adjacent a 0 n
  simp only [Int.zero_add] at this
  rw [this, integer_cast]
  constructor
  · intro h i j ⟨h1, h2, h3⟩
    have step : ∀ d : Nat, i + d < n + 1 → a i ≤ a (i + d) := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hd
        have := h (i + d) (by omega) (by omega)
        rw [show i + ((d + 1 : Nat) : Int) = i + d + 1 by omega]
        exact Int.le_trans (ih (by omega)) this
    have := step (j - i).toNat (by omega)
    rwa [show i + ((j - i).toNat : Int) = j by omega] at this
  · intro h k h1 h2; exact h k (k + 1) ⟨h1, by omega, by omega⟩

theorem perm_refl (a : Int → Int) : perm a a ↔ True :=
  iff_true_intro ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem perm_symm {a b : Int → Int} : perm a b → perm b a := by
  intro ⟨f, g, hgf, hfg, h⟩
  exact ⟨g, f, hfg, hgf, fun i => by rw [h (g i), hfg]⟩

theorem perm_trans {a b c : Int → Int} : perm a b → perm b c → perm a c := by
  intro ⟨f, g, hgf, hfg, h⟩ ⟨f', g', hgf', hfg', h'⟩
  exact ⟨fun i => f' (f i), fun i => g (g' i), fun i => by simp [hgf', hgf], fun i => by simp [hfg, hfg'],
    fun i => by rw [h, h']⟩

-- a permutation of a, b, gives the permutations of a those of b
theorem perm_congr {a b : Int → Int} (c : Int → Int) : perm a b → (perm a c ↔ perm b c) :=
  fun h => ⟨fun h' => perm_trans (perm_symm h) h', fun h' => perm_trans h h'⟩

theorem perm_swap_self (a : Int → Int) (p q : Int) :
    perm (fun j => if j = q then a p else (fun j => if j = p then a q else a j) j) a := by
  let t : Int → Int := fun j => if j = q then p else if j = p then q else j
  refine ⟨t, t, ?_, ?_, ?_⟩ <;> intro i <;> simp only [t] <;>
    by_cases h1 : i = q <;> by_cases h2 : i = p <;> by_cases h3 : p = q <;> simp_all

-- the elements of a swap, which unfolds to its two stores
theorem select_swap : Stmt.select_swap := by
  intro a p q j; rfl

theorem perm_swap (a b : Int → Int) (p q : Int) :
    perm (fun j => if j = q then a p else (fun j => if j = p then a q else a j) j) b ↔ perm a b :=
  perm_congr b (perm_swap_self a p q)

theorem perm_steps (a c : Int → Int) (ks : List Int) (F : (Int → Int) → Int → Int → Int) (n : Nat)
    (hks : length ks = n) :
    (∀ (b : Int → Int) (k : Int), perm (F b k) b)
      → (perm (current (trace a ks (fun b k => F b k))) c ↔ perm a c) := by
  intro hF
  induction ks generalizing a n with
  | nil => simp [trace, current]
  | cons k ks ih =>
    simp only [trace, current]
    rw [ih (F a k) ks.length rfl]
    exact perm_congr c (hF a k)

-- a trace of steps that each preserve the permutation, over any list of dependencies
theorem perm_steps_general {δ : Type} (a c : Int → Int) (ds : List δ) (f : (Int → Int) → δ → Int → Int) :
    (∀ (b : Int → Int) (d : δ), perm (f b d) b) → (perm (current (trace a ds f)) c ↔ perm a c) := by
  intro hf
  induction ds generalizing a with
  | nil => simp [trace, current]
  | cons d ds ih =>
    simp only [trace, current]
    rw [ih (f a d)]
    exact perm_congr c (hf a d)

theorem perm_steps_nat : Stmt.perm_steps_nat := by
  intro a c ks ns F n _ _ hF
  exact perm_steps_general a c (List.zip ks ns) _ (fun b ⟨k, nn⟩ => hF b k nn)

theorem perm_steps_three : Stmt.perm_steps_three := by
  intro a c ks ns is F n _ _ _ hF
  exact perm_steps_general a c (List.zip ks (List.zip ns is)) _ (fun b ⟨k, nn, i⟩ => hF b k nn i)

theorem perm_steps_two (a c : Int → Int) (ks is : List Int) (F : (Int → Int) → Int → Int → Int → Int) (n : Nat)
    (hks : length ks = n) (his : length is = n) :
    (∀ (b : Int → Int) (k : Int) (i : Int), perm (F b k i) b)
      → (perm (current (trace a (List.zip ks is) (fun b ⟨k, i⟩ => F b k i))) c ↔ perm a c) := by
  intro hF
  induction ks generalizing a is n with
  | nil => simp [trace, current]
  | cons k ks ih =>
    cases is with
    | nil => simp [trace, current]
    | cons i is =>
      rw [List.zip_cons_cons]; simp only [trace, current]
      rw [ih (F a k i) is ks.length rfl (by simp at hks his; omega)]
      exact perm_congr c (hF a k i)

theorem perm_swaps_one (a b : Int → Int) (ks : List Int) (P Q : (Int → Int) → Int → Int) (n : Nat)
    (hks : length ks = n) :
    perm (current (trace a ks (fun x k => fun j =>
        if j = Q x k then x (P x k) else (fun j => if j = P x k then x (Q x k) else x j) j))) b
      ↔ perm a b :=
  perm_steps a b ks _ n hks (fun x k => perm_swap_self x (P x k) (Q x k))

theorem perm_swaps (a b : Int → Int) (ks hs : List Int) (P Q : (Int → Int) → Int → Int → Int) (n : Nat)
    (hks : length ks = n) (hhs : length hs = n) :
    perm (current (trace a (List.zip ks hs) (fun x ⟨k, h⟩ => fun j =>
        if j = Q x k h then x (P x k h) else (fun j => if j = P x k h then x (Q x k h) else x j) j))) b
      ↔ perm a b :=
  perm_steps_two a b ks hs _ n hks hhs (fun x k h => perm_swap_self x (P x k h) (Q x k h))

theorem sorted_prefix_steps (a : Int → Int) (n : Int) (m : Nat) (F : (Int → Int) → Int → Int → Int) :
    n = integer m
      ∧ (∀ (b : Int → Int) (k : Int),
           0 ≤ k ∧ k < n ∧ sorted b 0 k ∧ partitioned b 0 k n
             → sorted (F b k) 0 (k + 1) ∧ partitioned (F b k) 0 (k + 1) n)
      → (sorted (current (trace a (butlast (counter 0 1 m)) (fun b k => F b k))) 0 n ↔ True) := by
  intro ⟨hn, hF⟩
  rw [integer_cast] at hn
  have : ∀ (r : Nat) (b : Int → Int) (k : Int), 0 ≤ k → k + r = n → sorted b 0 k ∧ partitioned b 0 k n →
      sorted (current (trace b (butlast (counter k 1 r)) (fun b k => F b k))) 0 n := by
    intro r
    induction r with
    | zero => intro b k _ hk h; simp only [counter, butlast, trace, current]; rw [← hk]; simpa using h.1
    | succ r ih =>
      intro b k h0 hk h
      rw [butlast_counter_succ]; simp only [trace, current]
      exact ih (F b k) (k + 1) (by omega) (by omega) (hF b k ⟨h0, by omega, h.1, h.2⟩)
  exact iff_true_intro (this m a 0 (by omega) (by omega)
    ⟨(sorted_empty a 0).2 trivial, (partitioned_empty a 0 n).2 trivial⟩)

theorem sorted_prefix_steps_two (a : Int → Int) (n : Int) (m : Nat) (F : (Int → Int) → Int → Int → Int → Int) :
    n ≤ integer m + 1
      ∧ (∀ (b : Int → Int) (k : Int) (i : Int), 0 ≤ i ∧ sorted b 0 i → sorted (F b k i) 0 (i + 1))
      → (sorted (current (trace a (List.zip (butlast (counter 0 1 m)) (butlast (counter 1 1 m)))
            (fun b ⟨k, i⟩ => F b k i))) 0 n ↔ True) := by
  intro ⟨hn, hF⟩
  rw [integer_cast] at hn
  have : ∀ (r : Nat) (b : Int → Int) (s : Int), 0 ≤ s → sorted b 0 (s + 1) →
      sorted (current (trace b (List.zip (butlast (counter s 1 r)) (butlast (counter (s + 1) 1 r)))
        (fun b ⟨k, i⟩ => F b k i))) 0 (s + 1 + r) := by
    intro r
    induction r with
    | zero => intro b s _ h; simpa [counter, butlast, trace, current] using h
    | succ r ih =>
      intro b s h0 h
      rw [butlast_counter_succ, butlast_counter_succ, List.zip_cons_cons]; simp only [trace, current]
      have := ih (F b s (s + 1)) (s + 1) (by omega) (hF b s (s + 1) ⟨by omega, h⟩)
      rwa [show s + 1 + 1 + (r : Int) = s + 1 + ((r + 1 : Nat) : Int) by omega] at this
  have := this m a 0 (by omega) ((sorted_short a 0 (0 + 1)) (by omega) |>.2 trivial)
  exact iff_true_intro (sorted_mono _ 0 _ n (by omega) this)

-- the cut and the partition points

theorem cutFrom_bounds (G : Int → Prop) (l : Int) (n : Nat) : l ≤ cutFrom G l n ∧ cutFrom G l n ≤ l + n := by
  induction n generalizing l with
  | zero => simp [cutFrom]
  | succ n ih =>
    simp only [cutFrom]
    split
    · have := ih (l + 1); omega
    · omega

theorem cutFrom_holds (G : Int → Prop) (l : Int) (n : Nat) : ∀ j, l ≤ j → j < cutFrom G l n → G j := by
  induction n generalizing l with
  | zero => simp [cutFrom]; intro j h1 h2; omega
  | succ n ih =>
    intro j h1 h2
    simp only [cutFrom] at h2
    split at h2
    · by_cases e : j = l
      · subst e; assumption
      · exact ih (l + 1) j (by omega) h2
    · omega

theorem cutFrom_fails (G : Int → Prop) (l : Int) (n : Nat) : cutFrom G l n < l + n → ¬G (cutFrom G l n) := by
  induction n generalizing l with
  | zero => simp [cutFrom]
  | succ n ih =>
    simp only [cutFrom]
    split
    · intro h; exact ih (l + 1) (by omega)
    · intro _; assumption

theorem cutFrom_mono (G G' : Int → Prop) (l : Int) (n : Nat) :
    (∀ j, G j → G' j) → cutFrom G l n ≤ cutFrom G' l n := by
  intro h
  induction n generalizing l with
  | zero => simp [cutFrom]
  | succ n ih =>
    simp only [cutFrom]
    split
    · rw [if_pos (h l (by assumption))]; exact ih (l + 1)
    · split
      · have := cutFrom_bounds G' (l + 1) n; omega
      · exact Int.le_refl _

-- the cut searches the h - l indices from l
theorem cut_toNat (G : Int → Prop) (l h : Int) : cut G l h = cutFrom G l (h - l).toNat := by
  simp only [cut, natural_eq]

theorem cut_bounds (G : Int → Prop) (l h : Int) : l ≤ h → l ≤ cut G l h ∧ cut G l h ≤ h := by
  intro hl; have := cutFrom_bounds G l (h - l).toNat; rw [cut_toNat]; omega

-- on a predicate that holds on a prefix of [l, h), the cut separates where it holds
theorem cut_iff (G : Int → Prop) (l h m : Int) :
    (∀ p q, l ≤ p → p ≤ q → q < h → G q → G p) → l ≤ m → m < h → (G m ↔ m < cut G l h) := by
  intro hG h1 h2
  have hb := cutFrom_bounds G l (h - l).toNat
  rw [cut_toNat]
  constructor
  · intro hm
    apply Classical.byContradiction
    intro hc
    exact cutFrom_fails G l (h - l).toNat (by omega) (hG _ m (by omega) (by omega) h2 hm)
  · intro hm; exact cutFrom_holds G l (h - l).toNat m h1 hm

theorem lower_iff (ar : Int → Int) (len y m : Int) :
    sorted ar 0 len → 0 ≤ m → m < len → (ar m < y ↔ m < lower ar len y) :=
  fun hs h1 h2 => cut_iff _ 0 len m (fun p q hp hpq hq hy => Int.lt_of_le_of_lt (hs p q ⟨hp, hpq, hq⟩) hy) h1 h2

theorem upper_iff (ar : Int → Int) (len y m : Int) :
    sorted ar 0 len → 0 ≤ m → m < len → (ar m ≤ y ↔ m < upper ar len y) :=
  fun hs h1 h2 => cut_iff _ 0 len m (fun p q hp hpq hq hy => Int.le_trans (hs p q ⟨hp, hpq, hq⟩) hy) h1 h2

theorem lower_rule (ar : Int → Int) (len y m : Int) :
    sorted ar 0 len ∧ 0 ≤ m ∧ m < len → (ar m < y ↔ m < lower ar len y) :=
  fun ⟨hs, h1, h2⟩ => lower_iff ar len y m hs h1 h2

theorem upper_rule (ar : Int → Int) (len y m : Int) :
    sorted ar 0 len ∧ 0 ≤ m ∧ m < len → (y < ar m ↔ upper ar len y ≤ m) := by
  intro ⟨hs, h1, h2⟩; have := upper_iff ar len y m hs h1 h2; omega

theorem lower_le (ar : Int → Int) (len y m : Int) :
    sorted ar 0 len ∧ 0 ≤ m ∧ m < len → (y ≤ ar m ↔ lower ar len y ≤ m) := by
  intro ⟨hs, h1, h2⟩; have := lower_iff ar len y m hs h1 h2; omega

theorem equal (ar : Int → Int) (len y m : Int) :
    sorted ar 0 len ∧ 0 ≤ m ∧ m < len → (ar m = y ↔ lower ar len y ≤ m ∧ m < upper ar len y) := by
  intro ⟨hs, h1, h2⟩
  have := lower_iff ar len y m hs h1 h2
  have := upper_iff ar len y m hs h1 h2
  omega

theorem bounds (ar : Int → Int) (len y : Int) :
    sorted ar 0 len ∧ 0 ≤ len → 0 ≤ lower ar len y ∧ lower ar len y ≤ upper ar len y ∧ upper ar len y ≤ len := by
  intro ⟨_, hl⟩
  have := cut_bounds (fun j => ar j < y) 0 len hl
  have := cut_bounds (fun j => ar j ≤ y) 0 len hl
  have := cutFrom_mono (fun j => ar j < y) (fun j => ar j ≤ y) 0 (len - 0).toNat (fun j h => Int.le_of_lt h)
  simp only [lower, upper, cut_toNat] at *
  omega

theorem cut_lower (ar : Int → Int) (len y : Int) :
    sorted ar 0 len ∧ 0 ≤ len → cut (fun (j : Int) => ar j < y) 0 len = lower ar len y :=
  fun _ => rfl

theorem lower_succ (ar : Int → Int) (len y : Int) : sorted ar 0 len → lower ar len (y + 1) = upper ar len y := by
  intro _
  simp only [lower, upper]
  congr 1; funext j; apply propext; omega

-- strides.dfy: induction over the remaining iterations, from the iteration s, with the read at j as the invariant

theorem trace_cons {α β : Type} (x : α) (d : β) (ds : List β) (f : α → β → α) :
    trace x (d :: ds) f = .step x (trace (f x d) ds f) := rfl

theorem current_step_eq {α : Type} [Inhabited α] (x : α) (t : Trace α) : current (.step x t) = current t := rfl

theorem current_trace_nil {α β : Type} [Inhabited α] (x : α) (f : α → β → α) : current (trace x [] f) = x := rfl

theorem stride2_from (X Y j : Int) (r : Nat) : ∀ (b : Int → Int) (s u : Int),
    current (trace b (List.zip (butlast (counter s 1 r)) (butlast (counter u 1 r)))
      (fun a ⟨k, i⟩ => fun j => if j = 2 * k + 1 then Y else (fun j => if j = 2 * k then X else a j) j)) j
      = (if 2 * s ≤ j ∧ j < 2 * (s + r) then if j % 2 = 0 then X else Y else b j) := by
  induction r with
  | zero => intro b s u; simp only [counter, butlast, List.zip_nil_left, current_trace_nil]; (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)
  | succ r ih =>
    intro b s u
    rw [butlast_counter_succ, butlast_counter_succ, List.zip_cons_cons, trace_cons, current_step_eq, ih]
    dsimp only
    (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)

theorem select_current_trace_stride2_zip (a0 : Int → Int) (n : Nat) (X Y j : Int) :
    current (trace a0 (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
      (fun a ⟨k, i⟩ => fun j => if j = 2 * k + 1 then Y else (fun j => if j = 2 * k then X else a j) j)) j
      = (if 0 ≤ j ∧ j < 2 * integer n then if j % 2 = 0 then X else Y else a0 j) := by
  rw [stride2_from, integer_cast]; simp only [Int.mul_zero, Int.zero_add]

theorem select_current_trace_stride2 : Stmt.select_current_trace_stride2 := by
  intro a0 n X Y j
  have h := select_current_trace_stride2_zip a0 n X Y j
  rw [trace_zip_self] at h
  exact h

theorem stride3_from (X Y Z j : Int) (r : Nat) : ∀ (b : Int → Int) (s u : Int),
    current (trace b (List.zip (butlast (counter s 1 r)) (butlast (counter u 1 r)))
      (fun a ⟨k, i⟩ => fun j => if j = 3 * k + 2 then Z else
        (fun j => if j = 3 * k + 1 then Y else (fun j => if j = 3 * k then X else a j) j) j)) j
      = (if 3 * s ≤ j ∧ j < 3 * (s + r) then if j % 3 = 0 then X else if j % 3 = 1 then Y else Z else b j) := by
  induction r with
  | zero => intro b s u; simp only [counter, butlast, List.zip_nil_left, current_trace_nil]; (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)
  | succ r ih =>
    intro b s u
    rw [butlast_counter_succ, butlast_counter_succ, List.zip_cons_cons, trace_cons, current_step_eq, ih]
    dsimp only
    (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)

theorem select_current_trace_stride3_zip (a0 : Int → Int) (n : Nat) (X Y Z j : Int) :
    current (trace a0 (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
      (fun a ⟨k, i⟩ => fun j => if j = 3 * k + 2 then Z else
        (fun j => if j = 3 * k + 1 then Y else (fun j => if j = 3 * k then X else a j) j) j)) j
      = (if 0 ≤ j ∧ j < 3 * integer n then if j % 3 = 0 then X else if j % 3 = 1 then Y else Z else a0 j) := by
  rw [stride3_from, integer_cast]; simp only [Int.mul_zero, Int.zero_add]

theorem select_current_trace_stride3 : Stmt.select_current_trace_stride3 := by
  intro a0 n X Y Z j
  have h := select_current_trace_stride3_zip a0 n X Y Z j
  rw [trace_zip_self] at h
  exact h

theorem stride2_cases_from (P Q : Prop) (X1 Y1 X2 Y2 X3 Y3 j : Int) (r : Nat) : ∀ (b : Int → Int) (s u : Int),
    current (trace b (List.zip (butlast (counter s 1 r)) (butlast (counter u 1 r)))
      (fun a ⟨k, i⟩ =>
        if P then fun j => if j = 2 * k + 1 then Y1 else (fun j => if j = 2 * k then X1 else a j) j
        else if Q then fun j => if j = 2 * k + 1 then Y2 else (fun j => if j = 2 * k then X2 else a j) j
        else fun j => if j = 2 * k + 1 then Y3 else (fun j => if j = 2 * k then X3 else a j) j)) j
      = (if 2 * s ≤ j ∧ j < 2 * (s + r) then
           if j % 2 = 0 then (if P then X1 else if Q then X2 else X3) else (if P then Y1 else if Q then Y2 else Y3)
         else b j) := by
  induction r with
  | zero => intro b s u; simp only [counter, butlast, List.zip_nil_left, current_trace_nil]; (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)
  | succ r ih =>
    intro b s u
    rw [butlast_counter_succ, butlast_counter_succ, List.zip_cons_cons, trace_cons, current_step_eq, ih]
    dsimp only
    (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)

theorem select_current_trace_stride2_cases_complete (a0 : Int → Int) (n : Nat) (P Q R : Prop) (X1 Y1 X2 Y2 X3 Y3 j : Int) :
    (R ↔ ¬P ∧ ¬Q) →
    current (trace a0 (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
      (fun a ⟨k, i⟩ =>
        if P then fun j => if j = 2 * k + 1 then Y1 else (fun j => if j = 2 * k then X1 else a j) j
        else if Q then fun j => if j = 2 * k + 1 then Y2 else (fun j => if j = 2 * k then X2 else a j) j
        else fun j => if j = 2 * k + 1 then Y3 else (fun j => if j = 2 * k then X3 else a j) j)) j
      = (if 0 ≤ j ∧ j < 2 * integer n then
           if j % 2 = 0 then (if P then X1 else if Q then X2 else X3) else (if P then Y1 else if Q then Y2 else Y3)
         else a0 j) := by
  intro _; rw [stride2_cases_from, integer_cast]; simp only [Int.mul_zero, Int.zero_add]

theorem select_current_trace_stride2_cases : Stmt.select_current_trace_stride2_cases := by
  intro a0 n P Q R X1 Y1 X2 Y2 X3 Y3 j hR
  have e : ∀ (A B C z : Int → Int), (if P then A else if Q then B else if R then C else z)
      = (if P then A else if Q then B else C) := by
    intro A B C z
    by_cases h1 : P
    · simp [h1]
    by_cases h2 : Q
    · simp [h1, h2]
    simp [h1, h2, hR.2 ⟨h1, h2⟩]
  simp only [e]
  have h := select_current_trace_stride2_cases_complete a0 n P Q R X1 Y1 X2 Y2 X3 Y3 j hR
  rw [trace_zip_self] at h
  exact h

theorem ahead_from (m : Int) (F G : Int → Int) (j : Int) (r : Nat) : ∀ (b : Int → Int) (s : Int), s + r ≤ m →
    current (trace b (List.zip (butlast (counter s 1 r)) (butlast (counter s 1 r)))
      (fun a ⟨k, i⟩ =>
        if k + 1 < m then fun j => if j = k then G k else (fun j => if j = k + 1 then F k else a j) j
        else fun j => if j = k then G k else a j)) j
      = (if s ≤ j ∧ j < s + r then G j else if j = s + r ∧ 0 < r ∧ j < m then F (j - 1) else b j) := by
  induction r with
  | zero => intro b s _; simp only [counter, butlast, List.zip_nil_left, current_trace_nil]; (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)
  | succ r ih =>
    intro b s hm
    rw [butlast_counter_succ, List.zip_cons_cons, trace_cons, current_step_eq, ih _ _ (by omega)]
    dsimp only
    (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)

theorem select_current_trace_ahead_complete (a0 : Int → Int) (n : Nat) (m : Int) (F G : Int → Int) (j : Int) :
    integer n ≤ m →
    current (trace a0 (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
      (fun a ⟨k, i⟩ =>
        if k + 1 < m then fun j => if j = k then G k else (fun j => if j = k + 1 then F k else a j) j
        else fun j => if j = k then G k else a j)) j
      = (if 0 ≤ j ∧ j < integer n then G j else if j = integer n ∧ 0 < j ∧ j < m then F (j - 1) else a0 j) := by
  intro h
  rw [integer_cast] at *
  rw [ahead_from m F G j n a0 0 (by omega)]
  (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)

-- the former statement over the counter twice (trace_zip_self)
theorem select_current_trace_ahead_zip :
  ∀ (a0 : Int → Int) (n : Nat) (m : Int) (F : Int → Int) (G : Int → Int) (j : Int),
    integer n ≤ m
      → current
        (trace
           a0
           (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
           (fun a ⟨k, i⟩ =>
              if k + 1 < m then
                fun j =>
                  if j = k then
                    G k
                  else
                    (fun j => if j = k + 1 then F k else a j) j
              else
                if m = k + 1 then
                  fun j => if j = k then G k else a j
                else
                  unspecified))
        j
        = (if 0 ≤ j ∧ j < integer n then
             G j
           else
             if j = integer n ∧ 0 < j ∧ j < m then F (j - 1) else a0 j) := by
  intro a0 n m F G j h
  have hn := h
  rw [integer_cast] at hn
  rw [trace_counter_congr a0 0 n _ _
    (fun a ⟨k, i⟩ =>
      if k + 1 < m then fun j => if j = k then G k else (fun j => if j = k + 1 then F k else a j) j
      else fun j => if j = k then G k else a j)
    (fun a k y h1 h2 => by
      dsimp only; by_cases e : k + 1 < m <;> simp only [e, ↓reduceIte]; rw [if_pos (show m = k + 1 by omega)])]
  exact select_current_trace_ahead_complete a0 n m F G j h

theorem select_current_trace_ahead : Stmt.select_current_trace_ahead := by
  intro a0 n m F G j
  have h := select_current_trace_ahead_zip a0 n m F G j
  rw [trace_zip_self] at h
  exact h

theorem ahead_down_from (F G : Int → Int) (j : Int) (r : Nat) : ∀ (b : Int → Int) (t s : Int),
    current (trace b (List.zip (butlast (counter t 1 r)) (butlast (counter s (-1) r)))
      (fun a ⟨k, i⟩ =>
        if 1 ≤ i then fun j => if j = i then G i else (fun j => if j = i + -1 then F i else a j) j
        else fun j => if j = i then G i else a j)) j
      = (if s - r < j ∧ j ≤ s then G j else if j = s - r ∧ 0 ≤ j ∧ 0 < r then F (j + 1) else b j) := by
  induction r with
  | zero => intro b t s; simp only [counter, butlast, List.zip_nil_left, current_trace_nil]; (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)
  | succ r ih =>
    intro b t s
    rw [butlast_counter_succ, butlast_counter_succ, List.zip_cons_cons, trace_cons, current_step_eq, ih]
    dsimp only
    (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)

theorem select_current_trace_ahead_down_complete (a0 : Int → Int) (n : Nat) (s : Int) (F G : Int → Int) (j : Int) :
    current (trace a0 (List.zip (butlast (counter 0 1 n)) (butlast (counter s (-1) n)))
      (fun a ⟨k, i⟩ =>
        if 1 ≤ i then fun j => if j = i then G i else (fun j => if j = i + -1 then F i else a j) j
        else fun j => if j = i then G i else a j)) j
      = (if s - integer n < j ∧ j ≤ s then G j
         else if j = s - integer n ∧ 0 ≤ j ∧ 0 < integer n then F (j + 1) else a0 j) := by
  rw [ahead_down_from, integer_cast]
  (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)

theorem select_current_trace_ahead_down : Stmt.select_current_trace_ahead_down := by
  intro a0 n s F G j
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  exact select_current_trace_ahead_down_complete a0 n s F G j

-- unsigned.dfy: the counters modulo m, by induction over the steps, whose values are the remainders of those of the
-- counter, (a % m + c) % m = (a + c) % m; the products n * c are atoms of omega, with the facts it needs about them

-- the update of mods does not read the iteration, so the trace is the same over any counter by 1
theorem mods_start (c m : Int) (n : Nat) : ∀ s i,
    trace i (butlast (counter s 1 n)) (fun x k => (x + c) % m) = mods i c m n := by
  induction n with
  | zero => intro s i; rfl
  | succ n ih =>
    intro s i; rw [butlast_counter_succ, trace_cons, ih]
    conv => rhs; rw [mods, butlast_counter_succ, trace_cons]
    rw [ih]

theorem mods_zero (i c m : Int) : mods i c m 0 = .stop i := rfl

theorem mods_succ (i c m : Int) (n : Nat) : mods i c m (n + 1) = .step i (mods ((i + c) % m) c m n) := by
  rw [mods, butlast_counter_succ, trace_cons, mods_start]

-- after at least one step, the current value is the remainder of that of the counter, whatever the initial value
theorem current_mods_succ (i c m : Int) (n : Nat) : current (mods i c m (n + 1)) = (i + ((n + 1 : Nat) : Int) * c) % m := by
  induction n generalizing i with
  | zero => rw [mods_succ, current_step_eq, mods_zero]; simp [current]
  | succ n ih =>
    rw [mods_succ, current_step_eq, ih, Int.emod_add_emod]
    congr 1; push_cast; simp only [Int.add_mul, Int.one_mul]; omega

theorem current_mods (i c m : Int) (n : Nat) : 0 ≤ i ∧ i < m → current (mods i c m n) = (i + integer n * c) % m := by
  intro ⟨h1, h2⟩
  rw [integer_cast]
  cases n with
  | zero => rw [mods_zero]; simp [current]; exact (Int.emod_eq_of_lt h1 h2).symm
  | succ n => exact current_mods_succ i c m n

theorem current_mods_up (i c m : Int) (n : Nat) :
    0 ≤ i + integer n * c ∧ i + integer n * c < m → current (mods i c m n) = i + integer n * c := by
  intro ⟨h1, h2⟩
  rw [integer_cast] at *
  cases n with
  | zero => rw [mods_zero]; simp [current]
  | succ n => rw [current_mods_succ]; exact Int.emod_eq_of_lt h1 h2

theorem butlast_mods_up (i c m : Int) (n : Nat) :
    0 ≤ i ∧ 0 ≤ c ∧ i + (integer n - 1) * c < m → butlast (mods i c m n) = butlast (counter i c n) := by
  intro ⟨h1, h2, h3⟩
  rw [integer_cast] at h3
  induction n generalizing i with
  | zero => rw [mods_zero]; rfl
  | succ n ih =>
    rw [mods_succ, butlast_counter_succ]
    cases n with
    | zero => rw [mods_zero]; rfl
    | succ k =>
      have hk : 0 ≤ (k : Int) * c := Int.mul_nonneg (by omega) h2
      push_cast at h3
      simp only [Int.sub_mul, Int.add_mul, Int.one_mul] at h3
      have e : (i + c) % m = i + c := Int.emod_eq_of_lt (by omega) (by omega)
      show i :: butlast (mods ((i + c) % m) c m (k + 1)) = i :: butlast (counter (i + c) c (k + 1))
      rw [e, ih (i + c) (by omega) (by push_cast; simp only [Int.sub_mul, Int.add_mul, Int.one_mul]; omega)]

theorem invs_mods_upper_cases (b i c m : Int) (n : Nat) :
    0 ≤ i ∧ i < m ∧ 0 < c ∧ b + c ≤ m
      → (invs (butlast (mods i c m n)) (fun x => x < b) ↔ n = zero ∨ i + (integer n - 1) * c < b) := by
  intro ⟨h1, h2, h3, h4⟩
  rw [integer_cast]
  induction n generalizing i with
  | zero => rw [mods_zero]; simp [butlast, invs]
  | succ n ih =>
    rw [mods_succ]
    show (i < b ∧ invs (butlast (mods ((i + c) % m) c m n)) (fun x => x < b)) ↔ _
    have hn : n = 0 → (n : Int) * c = 0 := by intro h; subst h; simp
    have hc : 0 ≤ (n : Int) * c := Int.mul_nonneg (by omega) (by omega)
    by_cases hb : i < b
    · have e : (i + c) % m = i + c := Int.emod_eq_of_lt (by omega) (by omega)
      have hih := ih (i + c) (by omega) (by omega)
      rw [e, propext hih]
      push_cast; simp only [Int.sub_mul, Int.add_mul, Int.one_mul]
      constructor
      · intro ⟨_, h⟩; right; rcases h with h | h
        · have := hn h; omega
        · omega
      · intro h; rcases h with h | h
        · exact h.elim
        · refine ⟨hb, ?_⟩; by_cases h0 : n = 0
          · exact Or.inl h0
          · right; omega
    · constructor
      · intro ⟨h, _⟩; exact absurd h hb
      · intro h; rcases h with h | h
        · exact absurd h (Nat.succ_ne_zero n)
        · push_cast at h; simp only [Int.sub_mul, Int.add_mul, Int.one_mul] at h; omega

theorem invs_mods_upper (b i c m : Int) (n : Nat) :
    0 ≤ i ∧ i < b ∧ 0 < c ∧ b + c ≤ m
      → (invs (butlast (mods i c m n)) (fun x => x < b) ↔ i + (integer n - 1) * c < b) := by
  intro ⟨h1, h2, h3, h4⟩
  rw [invs_mods_upper_cases b i c m n ⟨h1, by omega, h3, h4⟩]
  constructor
  · intro h; rcases h with h | h
    · subst h; simp [integer_cast]; omega
    · exact h
  · intro h; exact Or.inr h

theorem invs_mods_down_cases (i c m : Int) (n : Nat) :
    0 ≤ i ∧ i < m ∧ c < m ∧ i % (m - c) = 0
      → (invs (butlast (mods i c m n)) (fun x => 0 < x) ↔ n = zero ∨ 0 < i - (integer n - 1) * (m - c)) := by
  intro ⟨h1, h2, h3, h4⟩
  rw [integer_cast]
  induction n generalizing i with
  | zero => rw [mods_zero]; simp [butlast, invs]
  | succ n ih =>
    rw [mods_succ]
    show (0 < i ∧ invs (butlast (mods ((i + c) % m) c m n)) (fun x => 0 < x)) ↔ _
    have hd : 0 < m - c := by omega
    have hn : n = 0 → (n : Int) * (m - c) = 0 := by intro h; subst h; simp
    have hc : 0 ≤ (n : Int) * (m - c) := Int.mul_nonneg (by omega) (by omega)
    by_cases hi : 0 < i
    · have hdi : m - c ≤ i := Int.le_of_dvd hi (Int.dvd_of_emod_eq_zero h4)
      have e : (i + c) % m = i - (m - c) := by
        rw [show i + c = (i - (m - c)) + m by omega, Int.add_emod_right]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      have h4' : (i - (m - c)) % (m - c) = 0 :=
        Int.emod_eq_zero_of_dvd (Int.dvd_sub (Int.dvd_of_emod_eq_zero h4) (Int.dvd_refl _))
      have hih := ih (i - (m - c)) (by omega) (by omega) h4'
      rw [e, propext hih]
      push_cast; simp only [Int.sub_mul, Int.add_mul, Int.one_mul]
      constructor
      · intro ⟨_, h⟩; right; rcases h with h | h
        · have := hn h; omega
        · omega
      · intro h; rcases h with h | h
        · exact h.elim
        · refine ⟨hi, ?_⟩; by_cases h0 : n = 0
          · exact Or.inl h0
          · right; omega
    · constructor
      · intro ⟨h, _⟩; exact absurd h hi
      · intro h; rcases h with h | h
        · exact absurd h (Nat.succ_ne_zero n)
        · push_cast at h; simp only [Int.sub_mul, Int.add_mul, Int.one_mul] at h; omega

theorem invs_mods_down (i c m : Int) (n : Nat) :
    0 < i ∧ i < m ∧ c < m ∧ i % (m - c) = 0
      → (invs (butlast (mods i c m n)) (fun x => 0 < x) ↔ 0 < i - (integer n - 1) * (m - c)) := by
  intro ⟨h1, h2, h3, h4⟩
  rw [invs_mods_down_cases i c m n ⟨by omega, h2, h3, h4⟩]
  constructor
  · intro h; rcases h with h | h
    · subst h; simp [integer_cast]; omega
    · exact h
  · intro h; exact Or.inr h

theorem invs_counter_mod_upper_zero (b m : Int) (n : Nat) :
    0 < b ∧ b < m → (invs (butlast (counter 0 1 n)) (fun k => k % m < b) ↔ integer n - 1 < b) := by
  intro ⟨h1, h2⟩
  rw [invs_counter_forall, integer_cast]
  constructor
  · intro h
    apply Classical.byContradiction
    intro hc
    have := h b.toNat (by omega)
    rw [show (0 : Int) + (b.toNat : Int) = b by omega, Int.emod_eq_of_lt (by omega) h2] at this
    omega
  · intro h i hi
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

theorem invs_counter_mod_upper_cases (b i m : Int) (n : Nat) :
    0 ≤ i ∧ i < m ∧ b < m
      → (invs (butlast (counter 0 1 n)) (fun k => (k + i) % m < b) ↔ n = zero ∨ i + integer n - 1 < b) := by
  intro ⟨h1, h2, h3⟩
  rw [invs_counter_forall, integer_cast]
  constructor
  · intro h
    by_cases h0 : n = 0
    · exact Or.inl h0
    · right
      apply Classical.byContradiction
      intro hc
      by_cases hb : b ≤ i
      · have := h 0 (by omega)
        rw [show (0 : Int) + ((0 : Nat) : Int) + i = i by omega, Int.emod_eq_of_lt h1 h2] at this
        omega
      · have := h (b - i).toNat (by omega)
        rw [show (0 : Int) + ((b - i).toNat : Int) + i = b by omega, Int.emod_eq_of_lt (by omega) h3] at this
        omega
  · intro h k hk
    rcases h with h | h
    · subst h; exact absurd hk (Nat.not_lt_zero _)
    · rw [Int.emod_eq_of_lt (by omega) (by omega)]; omega

-- the trace of the remainders from y % m is the remainder of the trace from y, over any dependency
theorem trace_mod_add_const_from (m c : Int) (ds : List Int) : ∀ y,
    current (trace (y % m) ds (fun x k => (k + x + c) % m))
      = current (trace y ds (fun x k => k + x + c)) % m := by
  induction ds with
  | nil => intro y; rfl
  | cons d ds ih =>
    intro y
    rw [trace_cons, trace_cons, current_step_eq, current_step_eq]
    have e : (d + y % m + c) % m = (d + y + c) % m := by
      rw [show d + y % m + c = y % m + (d + c) by omega, show d + y + c = y + (d + c) by omega, Int.emod_add_emod]
    rw [e]
    exact ih (d + y + c)

theorem current_trace_mod_add_const : Stmt.current_trace_mod_add_const := by
  intro x0 n m c ⟨h1, h2⟩
  have := trace_mod_add_const_from m c (butlast (counter 0 1 n)) x0
  rwa [Int.emod_eq_of_lt h1 h2] at this

theorem trace_mod_add_cases_from (m : Int) (C : Int → Prop) (F : Int → Int) (ds : List Int) : ∀ y,
    current (trace (y % m) ds (fun x k => if C k then (x + F k) % m else x))
      = current (trace y ds (fun x k => if C k then x + F k else x)) % m := by
  induction ds with
  | nil => intro y; rfl
  | cons d ds ih =>
    intro y
    rw [trace_cons, trace_cons, current_step_eq, current_step_eq]
    by_cases hc : C d
    · simp only [hc, ↓reduceIte]
      rw [Int.emod_add_emod]
      exact ih (y + F d)
    · simp only [hc, ↓reduceIte]
      exact ih y

theorem current_trace_mod_add_cases : Stmt.current_trace_mod_add_cases := by
  intro x0 n m C F ⟨h1, h2⟩
  simp only [ite_lt_le, ite_le_lt, ite_eq_ne, ite_not_else, ite_ne_eq, ite_not_first]
  have := trace_mod_add_cases_from m C F (butlast (counter 0 1 n)) x0
  rwa [Int.emod_eq_of_lt h1 h2] at this

-- the bisection of search.dfy: a property that the update preserves holds of the current value; the bounds are such
-- properties, also with the third case, which keeps the state, so they need no premise on the steps

theorem current_trace_invariant {α β : Type} [Inhabited α] (P : α → Prop) (f : α → β → α)
    (hf : ∀ x d, P x → P (f x d)) : ∀ (ds : List β) (x : α), P x → P (current (trace x ds f))
  | [], x, hx => hx
  | d :: ds, x, hx => by
    rw [trace_cons, current_step_eq]
    exact current_trace_invariant P f hf ds (f x d) (hf x d hx)

theorem bisection_lo : Stmt.bisection_lo := by
  intro l0 h0 ks M G H n hks ⟨hl, hM, hG⟩
  have hc := cut_bounds G l0 h0 hl
  have key : l0 ≤ (current (bisection l0 h0 ks M G H)).1 ∧ (current (bisection l0 h0 ks M G H)).1 ≤ cut G l0 h0
      ∧ (current (bisection l0 h0 ks M G H)).2 ≤ h0 := by
    unfold bisection
    apply current_trace_invariant (fun (s : Int × Int) => l0 ≤ s.1 ∧ s.1 ≤ cut G l0 h0 ∧ s.2 ≤ h0)
    · rintro ⟨lo, hi⟩ k ⟨h1, h2, h3⟩
      dsimp only
      by_cases hA : lo < hi
      · have hm := hM lo hi hA
        by_cases hg : G (M lo hi)
        · have := (cut_iff G l0 h0 (M lo hi) (fun p q a b c d => hG p q ⟨a, b, c, d⟩) (by omega) (by omega)).1 hg
          simp only [hg, hA, and_self, ↓reduceIte]
          omega
        · by_cases hh : H (M lo hi)
          · simp only [hg, hh, hA, not_false_eq_true, and_self, false_and, ↓reduceIte]
            omega
          · simp only [hg, hh, hA, not_false_eq_true, and_self, false_and, and_true, or_self, not_true_eq_false,
              or_true, ↓reduceIte]
            omega
      · simp only [hA, and_false, false_and, not_false_eq_true, true_or, ↓reduceIte]
        omega
    · exact ⟨Int.le_refl _, hc.1, Int.le_refl _⟩
  exact ⟨key.1, key.2.1⟩

theorem bisection_hi : Stmt.bisection_hi := by
  intro l0 h0 ks M G H n hks ⟨hl, hM, hH⟩
  have hc := cut_bounds (fun j => ¬H j) l0 h0 hl
  have key : l0 ≤ (current (bisection l0 h0 ks M G H)).1
      ∧ cut (fun j => ¬H j) l0 h0 ≤ (current (bisection l0 h0 ks M G H)).2
      ∧ (current (bisection l0 h0 ks M G H)).2 ≤ h0 := by
    unfold bisection
    apply current_trace_invariant (fun (s : Int × Int) => l0 ≤ s.1 ∧ cut (fun j => ¬H j) l0 h0 ≤ s.2 ∧ s.2 ≤ h0)
    · rintro ⟨lo, hi⟩ k ⟨h1, h2, h3⟩
      dsimp only
      by_cases hA : lo < hi
      · have hm := hM lo hi hA
        by_cases hg : G (M lo hi)
        · simp only [hg, hA, and_self, ↓reduceIte]
          omega
        · by_cases hh : H (M lo hi)
          · have := (cut_iff (fun j => ¬H j) l0 h0 (M lo hi)
              (fun p q a b c d e => d (hH p q ⟨a, b, c, e⟩)) (by omega) (by omega))
            have : ¬(M lo hi < cut (fun j => ¬H j) l0 h0) := fun hlt => (this.2 hlt) hh
            simp only [hg, hh, hA, not_false_eq_true, and_self, false_and, ↓reduceIte]
            omega
          · simp only [hg, hh, hA, not_false_eq_true, and_self, false_and, and_true, or_self, not_true_eq_false,
              or_true, ↓reduceIte]
            omega
      · simp only [hA, and_false, false_and, not_false_eq_true, true_or, ↓reduceIte]
        omega
    · exact ⟨Int.le_refl _, hc.2, Int.le_refl _⟩
  exact ⟨key.2.1, key.2.2⟩

-- the lemmas of 0.46.12 (teq.dfy, arrays, aggregation)

theorem maps_counter_scale (b : Int) (i : Int) (c : Int) (n : Nat) :
    maps (butlast (counter i c n)) (fun v => b * v) = butlast (counter (b * i) (b * c) n) := by
  induction n generalizing i with
  | zero => rfl
  | succ m ih =>
    simp only [butlast_counter_succ, maps, ih]
    rw [Int.mul_add]

theorem store_select_other (a : Int → Int) (i : Int) (j : Int) (v : Int) :
    i ≠ j
      → (fun j1 => if j1 = j then a j else (fun j => if j = i then v else a j) j1)
        = (fun j => if j = i then v else a j) := by
  intro h
  funext j1
  by_cases e : j1 = j
  · subst e; simp [Ne.symm h]
  · simp [e]

-- from s ≥ 1 on, the position k is written from k - 1, which the previous step wrote: the value at j is the value at
-- s - 1 plus the sum of G over s, ..., j
theorem recurrence_from (G : Int → Int) (c : Int) (j : Int) : ∀ (m : Nat) (s : Int) (x : Int → Int), 1 ≤ s →
    current (trace x (butlast (counter s 1 m))
      (fun a i => if i = 0 then fun j => if j = 0 then c else a j
        else if 0 < i then fun j => if j = i then a (i - 1) + G i else a j else unspecified)) j
      = if s ≤ j ∧ j < s + m then x (s - 1) + sum (maps (butlast (counter s 1 (j - s + 1).toNat)) G) else x j := by
  intro m
  induction m with
  | zero => intro s x _; simp [counter, butlast, trace, current]; omega
  | succ t ih =>
    intro s x hs
    simp only [butlast_counter_succ, trace, current]
    rw [if_neg (by omega), if_pos (by omega), ih (s + 1) _ (by omega)]
    simp only [show s + 1 - 1 = s by omega, ↓reduceIte]
    by_cases hj : s ≤ j ∧ j < s + (t + 1 : Nat)
    · rw [if_pos hj]
      by_cases e : j = s
      · subst e
        rw [if_neg (by omega), if_pos rfl, show (j - j + 1).toNat = 0 + 1 by omega, sum_counter_succ]
        simp [counter, butlast, maps, sum]
      · rw [if_pos (by omega), show (j - s + 1).toNat = (j - (s + 1) + 1).toNat + 1 by omega, sum_counter_succ]
        omega
    · rw [if_neg hj, if_neg (by omega), if_neg (by omega)]

theorem select_current_trace_recurrence (a0 : Int → Int) (n : Nat) (c : Int) (j : Int) (G : Int → Int) :
    current (trace a0 (butlast (counter 0 1 n))
      (fun a i => if i = 0 then fun j => if j = 0 then c else a j
        else if 0 < i then fun j => if j = i then a (i - 1) + G i else a j else unspecified)) j
      = (if 0 ≤ j ∧ j < integer n then c + sum (maps (butlast (counter 1 1 (natural j))) (fun k => G k)) else a0 j) := by
  rw [integer_cast, natural_eq]
  cases n with
  | zero => simp [counter, butlast, trace, current]; omega
  | succ m =>
    simp only [butlast_counter_succ, trace, current, ↓reduceIte, Int.zero_add]
    rw [recurrence_from G c j m 1 _ (by omega)]
    push_cast
    by_cases e : j = 0
    · subst e; simp [counter, butlast, maps, sum]
    · by_cases hj : 1 ≤ j ∧ j < 1 + (m : Int)
      · rw [if_pos hj, if_pos (by omega), show (j - 1 + 1).toNat = j.toNat by omega]
      · rw [if_neg hj, if_neg e, if_neg (by omega)]

end TEQ
