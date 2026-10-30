-- the proofs of the lemmas of the database (Database.lean), each a theorem of the name of the lemma whose statement is
-- that of Stmt.<name> (checked in Check.lean); the counts of the database are integers, the proofs are those over
-- naturals of Naturals.lean, carried over by one bridge per definition: the definition over integers is the one over
-- naturals at toNat, since a count that is not positive is no step
import TEQ.Naturals

open Classical

set_option linter.unusedVariables false

noncomputable section

namespace TEQ

open List (nil cons length)
open Trace

-- the choices of the modules: -print lean prints guarded cases as conditionals that end in unspecified, whose last
-- guard is the complement of the others, hence the conditional without it
theorem cases_of {α : Type} [Inhabited α] {c d : Prop} [Decidable c] [Decidable d] {a b : α} (h : ¬c → d) :
    (if c then a else if d then b else unspecified) = if c then a else b := by
  by_cases hc : c
  · simp [hc]
  · simp [hc, h hc]

-- the guard of the last case is the complement of the others, by arithmetic or literally
macro "complement" : tactic => `(tactic| first | exact id | (intro; omega) |
  (intro h; simp only [Classical.not_and_iff_not_or_not, Int.not_lt] at h; assumption))

-- the choices of a goal as conditionals
macro "choices" : tactic => `(tactic| simp (disch := complement) only [cases_of])

-- the bridges

theorem counter_N (i c n : Int) : counter i c n = N.counter i c n.toNat := by
  rw [counter]
  split
  · rw [show n.toNat = 0 by omega]; rfl
  · rw [show n.toNat = (n - 1).toNat + 1 by omega, counter_N (i + c) c (n - 1)]; rfl
termination_by n.toNat
decreasing_by omega

theorem consts_N {α : Type} [Inhabited α] (n : Int) (v : α) : consts n v = N.consts n.toNat v := by
  rw [consts]
  split
  · rw [show n.toNat = 0 by omega]; rfl
  · rw [show n.toNat = (n - 1).toNat + 1 by omega, consts_N (n - 1) v]; rfl
termination_by n.toNat
decreasing_by omega

theorem cutFrom_N (G : Int → Prop) (l n : Int) : cutFrom G l n = N.cutFrom G l n.toNat := by
  rw [cutFrom]
  split
  · rw [show n.toNat = 0 by omega]; rfl
  · rw [show n.toNat = (n - 1).toNat + 1 by omega, cutFrom_N G (l + 1) (n - 1)]; rfl
termination_by n.toNat
decreasing_by omega

theorem pow_N (c n : Int) : pow c n = N.pow c n.toNat := by
  rw [pow]
  split
  · rw [show n.toNat = 0 by omega]; rfl
  · rw [show n.toNat = (n - 1).toNat + 1 by omega, pow_N c (n - 1)]; rfl
termination_by n.toNat
decreasing_by omega

theorem prefix_N {α : Type} [Inhabited α] (k : Int) (xs : List α) : «prefix» k xs = N.«prefix» k.toNat xs := by
  induction xs generalizing k with
  | nil => cases k.toNat <;> rfl
  | cons x ys ih =>
    simp only [«prefix»]
    split
    · rw [show k.toNat = 0 by omega]; rfl
    · rw [show k.toNat = (k - 1).toNat + 1 by omega, ih]; rfl

-- a read at a negative position is unspecified, as one beyond the end
theorem earlier_N {α : Type} [Inhabited α] (k : Int) (xs : List α) :
    earlier k xs = if k < 0 then unspecified else N.earlier k.toNat xs := by
  induction xs generalizing k with
  | nil => split <;> (try cases k.toNat) <;> rfl
  | cons x ys ih =>
    simp only [earlier]
    by_cases h : k < 0
    · simp [h]
    · by_cases h0 : k = 0
      · subst h0; rfl
      · rw [if_neg h, if_neg h, if_neg h0, ih, if_neg (by omega),
          show k.toNat = (k - 1).toNat + 1 by omega]; rfl

theorem earlier_N_nonneg {α : Type} [Inhabited α] (k : Int) (xs : List α) (h : 0 ≤ k) :
    earlier k xs = N.earlier k.toNat xs := by
  rw [earlier_N, if_neg (by omega)]

theorem indexof_N {α : Type} [Inhabited α] (x : α) (xs : List α) : indexof x xs = (N.indexof x xs : Int) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp only [indexof, N.indexof]
    split
    · rw [ih]; show _ = ((N.indexof x ys + 1 : Nat) : Int); omega
    · rfl

theorem cut_N (G : Int → Prop) (l h : Int) : cut G l h = N.cut G l h := by
  rw [cut, N.cut_toNat, cutFrom_N]

theorem lower_N (ar : Int → Int) (len y : Int) : lower ar len y = N.lower ar len y := by
  simp only [lower, N.lower, cut_N]

theorem upper_N (ar : Int → Int) (len y : Int) : upper ar len y = N.upper ar len y := by
  simp only [upper, N.upper, cut_N]

theorem mods_N (i c m n : Int) : mods i c m n = N.mods i c m n.toNat := by
  simp only [mods, N.mods, counter_N]

-- multisets: the multiset of the elements of a list is its class, whose aggregates are the folds of the list of
-- Naturals.lean
theorem elems_mk {α : Type} [Inhabited α] (xs : List α) : elems xs = Bag.mk xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => rw [elems, ih]; rfl

theorem sum_mk (xs : List Int) : sum (Bag.mk xs) = N.sum xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih => show v + sum (Bag.mk vs) = _; rw [ih, N.sum]

theorem parity_mk (xs : List Int) : parity (Bag.mk xs) = N.parity xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih => show (if v % 2 = 0 then 1 else -1) + parity (Bag.mk vs) = _; rw [ih, N.parity]

theorem count_mk {α : Type} [Inhabited α] (xs : List α) (e : α) : Bag.count (Bag.mk xs) e = N.count e xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih =>
    have ih' : ((vs.count e : Nat) : Int) = N.count e vs := ih
    show ((List.count e (v :: vs) : Nat) : Int) = _
    rw [List.count_cons, N.count, Int.natCast_add, ih']
    by_cases h : v = e <;> simp [h] <;> omega

theorem sum_N (xs : List Int) : sum (elems xs) = N.sum xs := by rw [elems_mk, sum_mk]

theorem parity_N (xs : List Int) : parity (elems xs) = N.parity xs := by rw [elems_mk, parity_mk]

theorem count_N {α : Type} [Inhabited α] (xs : List α) (e : α) : Bag.count (elems xs) e = N.count e xs := by
  rw [elems_mk, count_mk]

-- the accessors of folds: the j-th earlier state of a trace is the result of the first j updates, and the prefix of
-- its states that of the trace over the prefix of its dependency
theorem earlier_trace_int {α β : Type} [Inhabited α] [Inhabited β] (j : Int) (x : α) (ds : List β) (f : α → β → α)
    (h0 : 0 ≤ j) (h1 : j < ds.length) :
    earlier j (butlast (trace x ds f)) = current (trace x («prefix» j ds) f) := by
  rw [earlier_N_nonneg j _ h0, prefix_N]; exact N.earlier_butlast_trace _ _ _ _ (by omega)

theorem prefix_trace_int {α β : Type} [Inhabited α] [Inhabited β] (k : Int) (x : α) (ds : List β) (f : α → β → α) :
    «prefix» k (butlast (trace x ds f)) = butlast (trace x («prefix» k ds) f) := by
  rw [prefix_N, prefix_N]; exact N.prefix_butlast_trace _ _ _ _

theorem prefix_zip_int {α β : Type} [Inhabited α] [Inhabited β] (k : Int) (xs : List α) (ys : List β) :
    «prefix» k (List.zip xs ys) = List.zip («prefix» k xs) («prefix» k ys) := by
  rw [prefix_N, prefix_N, prefix_N]; exact N.prefix_zip _ _ _

-- the prefix of a counter zipped with a list of its length: the shorter counter, which zip cuts to the prefix of the
-- list also where the prefix is longer than the list
theorem prefix_zip_counter {β : Type} [Inhabited β] (c : Int) (k : Nat) : ∀ (i : Int) (n : Nat) (ys : List β),
    ys.length = n →
    N.«prefix» k (List.zip (butlast (N.counter i c n)) ys) = List.zip (butlast (N.counter i c k)) (N.«prefix» k ys) := by
  induction k with
  | zero => intro i n ys h; rfl
  | succ k ih =>
    intro i n ys h
    cases ys with
    | nil => simp [N.«prefix»]
    | cons y ys =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; omega⟩
      rw [N.butlast_counter_succ, N.butlast_counter_succ, List.zip_cons_cons]
      simp only [N.«prefix», List.zip_cons_cons]
      rw [ih (i + c) m ys (by simpa using h)]

theorem squares_N (i n : Int) : squares i n = N.squares i n.toNat := by
  simp only [squares, N.squares, counter_N, sum_N]

theorem cubes_N (i n : Int) : cubes i n = N.cubes i n.toNat := by
  simp only [cubes, N.cubes, counter_N, sum_N]

theorem fourths_N (i n : Int) : fourths i n = N.fourths i n.toNat := by
  simp only [fourths, N.fourths, counter_N, sum_N]

theorem fifths_N (i n : Int) : fifths i n = N.fifths i n.toNat := by
  simp only [fifths, N.fifths, counter_N, sum_N]

theorem series_N (x0 z a n : Int) : series x0 z a n = N.series x0 z a n.toNat := by
  simp only [series, N.series, counter_N]

theorem above_iterations_N (n : Int) (ts : List Int) : above_iterations n ts = N.above_iterations n.toNat ts := by
  simp only [above_iterations, N.above_iterations, counter_N]

-- conditionals on equivalent conditions, e.g. a count of naturals at toNat and the integer one
theorem ite_iff {α : Type} {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) (a b : α) :
    (if p then a else b) = (if q then a else b) := by
  by_cases hp : p
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

-- a count of naturals at toNat is zero where the integer one is not positive
theorem toNat_zero_iff (n : Int) : (n.toNat = Nat.zero) ↔ n ≤ 0 := by
  show n.toNat = 0 ↔ _; omega

-- an integer that is not negative is a natural
theorem nat_or_neg (n : Int) : (∃ m : Nat, n = m) ∨ n < 0 := by
  rcases Int.lt_or_le n 0 with h | h
  · exact Or.inr h
  · exact Or.inl ⟨n.toNat, (Int.toNat_of_nonneg h).symm⟩

-- invariants over a counter hold alike for predicates that agree on its values, e.g. reads at positions that are not
-- negative, where the reads over integers are those over naturals
theorem invs_counter_congr (s : Int) (m : Nat) (f g : Int → Prop) (h : ∀ k, s ≤ k → (f k ↔ g k)) :
    invs (butlast (N.counter s 1 m)) f ↔ invs (butlast (N.counter s 1 m)) g := by
  induction m generalizing s with
  | zero => rfl
  | succ t ih =>
    simp only [N.butlast_counter_succ, invs]
    rw [ih (s + 1) (fun k hk => h k (by omega)), h s (Int.le_refl s)]

-- the iteration constraint that lists agree at the iterations of a loop, over integers and over naturals
theorem agree_prefix_N (n : Int) (xs ys : List Int) :
    invs (butlast (counter 0 1 n)) (fun k => earlier k xs = earlier k ys) ↔ N.agree_prefix n.toNat xs ys := by
  simp only [N.agree_prefix, counter_N]
  exact invs_counter_congr 0 n.toNat _ _ (fun k hk => by
    rw [earlier_N_nonneg k xs hk, earlier_N_nonneg k ys hk, N.natural_eq])

-- the lemmas of teq.dfy

theorem maps_identity : Stmt.maps_identity := by
  intro α _ xs n hxs; exact N.maps_identity xs xs.length rfl

theorem counter_def : Stmt.counter_def := by
  intro i c n; rw [counter_N, counter_N]; exact N.counter_def i c n.toNat

theorem consts_def : Stmt.consts_def := by
  intro α _ x i c n; rw [counter_N, consts_N]; exact N.consts_def x i c n.toNat

theorem maps_earlier : Stmt.maps_earlier := by
  intro α _ n xs hxs
  rw [counter_N, prefix_N, N.maps_counter_congr_gen 0 n.toNat (fun k => earlier k xs)
    (fun k => N.earlier (N.natural k) xs) (fun k hk => by simp only [earlier_N_nonneg k xs (by omega), N.natural_eq])]
  exact N.maps_earlier n.toNat xs (by rw [N.integer_cast, N.integer_cast]; omega)

theorem earlier_prefix : Stmt.earlier_prefix := by
  intro α _ j k xs h
  by_cases hj : 0 ≤ j
  · rw [earlier_N_nonneg j _ hj, earlier_N_nonneg j _ hj, prefix_N]
    exact N.earlier_prefix j.toNat k.toNat xs (by rw [N.integer_cast, N.integer_cast]; omega)
  · rw [earlier_N, earlier_N]; simp [show j < 0 by omega]

theorem maps_counter_affine : Stmt.maps_counter_affine := by
  intro a b i c n; rw [counter_N, counter_N]; exact N.maps_counter_affine a b i c n.toNat

theorem maps_counter_scale : Stmt.maps_counter_scale := by
  intro b i c n; rw [counter_N, counter_N]; exact N.maps_counter_scale b i c n.toNat

theorem invs_const : Stmt.invs_const := by
  intro b i c n; rw [counter_N, N.invs_const]; show n.toNat = 0 ∨ b ↔ _
  rw [show (n.toNat = 0) = (n ≤ 0) from propext (by omega)]

theorem invs_counter_lower : Stmt.invs_counter_lower := by
  intro m i c n
  rw [counter_N, N.invs_counter_lower, N.integer_cast]
  show n.toNat = 0 ∨ _ ↔ _
  by_cases hn : n ≤ 0
  · constructor <;> intro _ <;> omega
  · rw [Int.toNat_of_nonneg (by omega)]; constructor <;> intro h <;> omega

theorem distincts_counter : Stmt.distincts_counter := by
  intro i c n; rw [counter_N]; exact N.distincts_counter i c n.toNat

theorem invs_counter_upper_nonnegative : Stmt.invs_counter_upper_nonnegative := by
  intro m n hm; rw [counter_N, N.invs_counter_upper_nonnegative m n.toNat hm, N.integer_cast]
  constructor <;> intro _ <;> omega

theorem invs_counter_upper : Stmt.invs_counter_upper := by
  intro m i c n
  rw [counter_N, N.invs_counter_upper, N.integer_cast]
  show n.toNat = 0 ∨ _ ↔ _
  by_cases hn : n ≤ 0
  · constructor <;> intro _ <;> omega
  · rw [Int.toNat_of_nonneg (by omega)]; constructor <;> intro h <;> omega

theorem current_counter : Stmt.current_counter := by
  intro i c n hn; rw [counter_N, N.current_counter, N.integer_cast, Int.toNat_of_nonneg hn]

theorem earlier_counter : Stmt.earlier_counter := by
  intro k i c n ⟨hk, hkn⟩
  rw [earlier_N_nonneg k _ hk, counter_N, N.earlier_counter k.toNat i c n.toNat
    (by rw [N.integer_cast, N.integer_cast]; omega), N.integer_cast, Int.toNat_of_nonneg hk]

theorem prefix_counter : Stmt.prefix_counter := by
  intro k i c n h
  rw [prefix_N, counter_N, counter_N]
  exact N.prefix_counter k.toNat i c n.toNat (by rw [N.integer_cast, N.integer_cast]; omega)

theorem occurs_counter_up : Stmt.occurs_counter_up := by
  intro j i n; rw [counter_N, N.occurs_counter_up, N.integer_cast]; constructor <;> intro _ <;> omega

theorem maps_counter_neg : Stmt.maps_counter_neg := by
  intro a i c n; rw [counter_N, counter_N]
  induction n.toNat generalizing i with
  | zero => rfl
  | succ m ih => simp only [N.butlast_counter_succ, maps, ih, show a - (i + c) = a - i + -c by omega]

-- a constant trace cut at k ≤ n is the constant trace of k steps
theorem prefix_consts_N {α : Type} [Inhabited α] (x : α) : ∀ (k n : Nat), k ≤ n →
    N.«prefix» k (butlast (N.consts n x)) = butlast (N.consts k x)
  | 0, n, _ => by cases n <;> rfl
  | k + 1, 0, h => absurd h (by omega)
  | k + 1, n + 1, h => by
    simp only [N.consts, butlast, N.«prefix»]; rw [prefix_consts_N x k n (by omega)]

theorem prefix_consts : Stmt.prefix_consts := by
  intro k n x h; rw [prefix_N, consts_N, consts_N]; exact prefix_consts_N x k.toNat n.toNat (by omega)

theorem occurs_counter_down_N (j : Int) (n : Nat) : ∀ (i : Int),
    occurs j (butlast (N.counter i (-1) n)) ↔ i - n < j ∧ j ≤ i := by
  induction n with
  | zero => intro i; (simp [N.counter, butlast, occurs]) <;> omega
  | succ m ih => intro i; simp only [N.butlast_counter_succ, occurs, ih]; omega

theorem occurs_counter_down : Stmt.occurs_counter_down := by
  intro j i n; rw [counter_N, occurs_counter_down_N]; omega

theorem indexof_counter_up : Stmt.indexof_counter_up := by
  intro j i n h
  rw [indexof_N, counter_N, N.indexof_counter_up j i n.toNat (by rw [N.integer_cast]; omega), N.natural_eq]
  omega

theorem maps_const : Stmt.maps_const := by
  intro α _ x i c n; rw [counter_N, consts_N]; exact N.maps_const x i c n.toNat

theorem prefix_maps_counter : Stmt.prefix_maps_counter := by
  intro k i c n ys F hys h
  rw [prefix_N, counter_N, counter_N]
  exact N.prefix_maps_counter k.toNat i c n.toNat ys F (by omega) (by rw [N.integer_cast, N.integer_cast]; omega)

theorem butlast_counter_nil : Stmt.butlast_counter_nil := by
  intro i c n; rw [counter_N, N.butlast_counter_nil]; show n.toNat = 0 ↔ _; omega

theorem butlast_counter_consts_N (i c v : Int) (m : Nat) :
    butlast (N.counter i c m) = butlast (N.consts m v) ↔ m = 0 ∨ i = v ∧ (m ≤ 1 ∨ c = 0) := by
  induction m generalizing i with
  | zero => simp [N.counter, N.consts, butlast]
  | succ m ih => simp only [N.counter, N.consts, butlast, List.cons.injEq, ih]; omega

theorem butlast_counter_consts : Stmt.butlast_counter_consts := by
  intro i c n v; rw [counter_N, consts_N, butlast_counter_consts_N]; omega

theorem current_consts : Stmt.current_consts := by
  intro α _ n x; rw [consts_N]; exact N.current_consts n.toNat x

theorem earlier_consts : Stmt.earlier_consts := by
  intro α _ k n x ⟨hk, hkn⟩
  rw [earlier_N_nonneg k _ hk, consts_N]
  exact N.earlier_consts k.toNat n.toNat x (by rw [N.integer_cast, N.integer_cast]; omega)

-- lengths: the database's length is the integer of List.length, a trace over a list has one earlier state per value

theorem length_nil : Stmt.length_nil := by intro α _; rfl

theorem length_cons : Stmt.length_cons := by intro α _ x xs; simp

theorem length_eq_zero : Stmt.length_eq_zero := by
  intro α _ xs
  cases xs with
  | nil => simp
  | cons y ys => simp

theorem length_counter : Stmt.length_counter := by
  intro i c n hn; rw [counter_N, N.length_butlast_counter]; omega

theorem length_butlast_consts_N {α : Type} [Inhabited α] (m : Nat) (x : α) : (butlast (N.consts m x)).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [N.consts, butlast, List.length_cons, ih]

theorem length_consts : Stmt.length_consts := by
  intro α _ n x hn; rw [consts_N, length_butlast_consts_N]; omega

theorem length_prefix : Stmt.length_prefix := by
  intro α _ k xs ⟨hk, hkl⟩
  rw [prefix_N, N.length_prefix k.toNat xs (by omega)]; omega

theorem prefix_length : Stmt.prefix_length := by
  intro α _ k xs h
  induction xs generalizing k with
  | nil => rfl
  | cons x ys ih =>
    simp only [List.length_cons] at h
    simp only [«prefix»]
    rw [if_neg (by omega), ih (k - 1) (by omega)]

theorem length_maps : Stmt.length_maps := by
  intro α β _ _ xs F n hxs; rw [N.length_maps]

theorem length_maps_deps : Stmt.length_maps_deps := by
  intro α β γ _ _ _ xs ys F n hxs hys h
  rw [N.length_maps, N.length_zip_eq xs ys xs.length rfl (by omega)]

theorem length_selects : Stmt.length_selects := by
  intro α β _ _ a keys n hkeys; rw [selects, N.length_maps]

theorem length_stores : Stmt.length_stores := by
  intro α β _ _ a keys values n hkeys hvalues h
  rw [stores, N.length_butlast_trace, N.length_zip_eq keys values keys.length rfl (by omega)]

theorem consts_choice : Stmt.consts_choice := by
  intro α _ n xs c hxs; rw [counter_N, consts_N]; exact N.consts_choice n.toNat xs c (by omega)

theorem selects_nil : Stmt.selects_nil := N.selects_nil

theorem earlier_selects : Stmt.earlier_selects := by
  intro α β _ _ j a keys n hkeys ⟨hj, hjn⟩
  rw [earlier_N_nonneg j _ hj, earlier_N_nonneg j _ hj]
  exact N.earlier_selects j.toNat a keys n.toNat (by omega) (by rw [N.integer_cast, N.integer_cast]; omega)

theorem current_stores : Stmt.current_stores := by
  unfold Stmt.current_stores; choices
  intro α β _ _ k a keys values n hkeys hvalues
  rw [indexof_N, earlier_N_nonneg _ _ (by omega), Int.toNat_natCast]
  exact N.current_stores k a keys values n.toNat (by omega) (by omega)

theorem earlier_stores : Stmt.earlier_stores := by
  unfold Stmt.earlier_stores; choices
  intro α β _ _ k j a keys values n hkeys hvalues ⟨hj, hjn⟩
  rw [earlier_N_nonneg j _ hj, prefix_N, indexof_N, earlier_N_nonneg _ _ (by omega), Int.toNat_natCast]
  exact N.earlier_stores k j.toNat a keys values n.toNat (by omega) (by omega)
    (by rw [N.integer_cast, N.integer_cast]; omega)

theorem length_shifts : Stmt.length_shifts := by
  intro a keys n hkeys; rw [shifts, N.length_butlast_trace]

theorem earlier_shifts : Stmt.earlier_shifts := by
  intro j a keys n hkeys ⟨hj, hjn⟩; rw [shifts, shifts, earlier_trace_int j _ _ _ hj (by omega)]

theorem prefix_shifts : Stmt.prefix_shifts := by
  intro k a keys n hkeys; rw [shifts, shifts, prefix_trace_int]

-- the lemmas of aggregation.dfy

theorem current_sums : Stmt.current_sums := by
  intro x values n hvalues; simp only [sum_N] at *; exact N.current_sums x values values.length rfl

theorem earlier_sums : Stmt.earlier_sums := by
  intro j x values n hvalues ⟨hj, hjn⟩; simp only [sum_N] at *
  rw [earlier_N_nonneg j _ hj, prefix_N]
  exact N.earlier_sums j.toNat x values n.toNat (by omega) (by rw [N.integer_cast, N.integer_cast]; omega)

theorem prefix_sums : Stmt.prefix_sums := by
  intro k x values n hvalues; rw [prefix_N, prefix_N]; exact N.prefix_sums k.toNat x values values.length rfl

-- the laws of the operations on multisets, over the lists of their classes
theorem sum_append (xs ys : List Int) : N.sum (xs ++ ys) = N.sum xs + N.sum ys := by
  induction xs with
  | nil => simp [N.sum]
  | cons v vs ih => simp only [List.cons_append, N.sum, ih]; omega

theorem parity_append (xs ys : List Int) : N.parity (xs ++ ys) = N.parity xs + N.parity ys := by
  induction xs with
  | nil => simp [N.parity]
  | cons v vs ih => simp only [List.cons_append, N.parity, ih]; omega

theorem count_append {α : Type} [Inhabited α] (e : α) (xs ys : List α) :
    N.count e (xs ++ ys) = N.count e xs + N.count e ys := by
  induction xs with
  | nil => simp [N.count]
  | cons v vs ih => simp only [List.cons_append, N.count, ih]; omega

-- a submultiset and the difference to it make up the multiset, since the difference cuts off at zero only below it
theorem diff_append {α : Type} [Inhabited α] (xs ys : List α) (h : Bag.mk ys ≤ Bag.mk xs) :
    Bag.mk (Bag.diff xs ys ++ ys) = Bag.mk xs := by
  apply Quotient.sound
  apply List.perm_iff_count.2
  intro e
  have he : ((ys.count e : Nat) : Int) ≤ ((xs.count e : Nat) : Int) := h e
  rw [List.count_append, Bag.count_diff]
  omega

theorem sum_empty : Stmt.sum_empty := rfl

theorem sum_single : Stmt.sum_single := by
  intro x; show x + 0 = x; omega

theorem sum_union : Stmt.sum_union := by
  intro m n
  induction m using Quotient.ind; induction n using Quotient.ind
  exact (sum_mk _).trans ((sum_append _ _).trans (by rw [← sum_mk, ← sum_mk]; rfl))

theorem sum_difference : Stmt.sum_difference := by
  intro m n h
  induction m using Quotient.ind; induction n using Quotient.ind
  rename_i xs ys
  have hs := congrArg sum (diff_append xs ys h)
  rw [sum_mk, sum_mk, sum_append] at hs
  show sum (Bag.mk (Bag.diff xs ys)) = sum (Bag.mk xs) - sum (Bag.mk ys)
  rw [sum_mk, sum_mk, sum_mk]; omega

theorem parity_empty : Stmt.parity_empty := rfl

theorem parity_single : Stmt.parity_single := by
  unfold Stmt.parity_single; choices
  intro x; show (if x % 2 = 0 then 1 else -1) + 0 = _; omega

theorem parity_union : Stmt.parity_union := by
  intro m n
  induction m using Quotient.ind; induction n using Quotient.ind
  exact (parity_mk _).trans ((parity_append _ _).trans (by rw [← parity_mk, ← parity_mk]; rfl))

theorem parity_difference : Stmt.parity_difference := by
  intro m n h
  induction m using Quotient.ind; induction n using Quotient.ind
  rename_i xs ys
  have hs := congrArg parity (diff_append xs ys h)
  rw [parity_mk, parity_mk, parity_append] at hs
  show parity (Bag.mk (Bag.diff xs ys)) = parity (Bag.mk xs) - parity (Bag.mk ys)
  rw [parity_mk, parity_mk, parity_mk]; omega

theorem multiplicity_empty : Stmt.multiplicity_empty := by
  intro α _ e; rfl

theorem multiplicity_single : Stmt.multiplicity_single := by
  unfold Stmt.multiplicity_single; choices
  intro α _ v e
  show Bag.count (Bag.mk [v]) e = _
  rw [count_mk, N.count, N.count]; split <;> omega

theorem multiplicity_union : Stmt.multiplicity_union := by
  intro α _ m n e
  induction m using Quotient.ind; induction n using Quotient.ind
  exact (count_mk _ e).trans ((count_append e _ _).trans (by rw [← count_mk, ← count_mk]; rfl))

theorem multiplicity_difference : Stmt.multiplicity_difference := by
  intro α _ m n e h
  induction m using Quotient.ind; induction n using Quotient.ind
  rename_i xs ys
  have he : ((ys.count e : Nat) : Int) ≤ ((xs.count e : Nat) : Int) := h e
  show ((List.count e (Bag.diff xs ys) : Nat) : Int) = ((xs.count e : Nat) : Int) - ((ys.count e : Nat) : Int)
  rw [Bag.count_diff]; omega

theorem max_empty : Stmt.max_empty := by
  intro x; rfl

theorem max_single : Stmt.max_single := by
  unfold Stmt.max_single; choices
  intro x v; rfl

-- the maximum and the minimum over a union are the folds over the elements of the second operand first, since the
-- fold is a right fold that does not depend on the order
theorem max_union : Stmt.max_union := by
  intro x m n
  induction m using Quotient.ind; induction n using Quotient.ind
  rename_i xs ys
  show max x (Bag.mk (xs ++ ys)) = _
  rw [show Bag.mk (xs ++ ys) = Bag.mk (ys ++ xs) from Quotient.sound List.perm_append_comm]
  show List.foldr _ x (ys ++ xs) = _
  rw [List.foldr_append]; rfl

theorem min_empty : Stmt.min_empty := by
  intro x; rfl

theorem min_single : Stmt.min_single := by
  unfold Stmt.min_single; choices
  intro x v; rfl

theorem min_union : Stmt.min_union := by
  intro x m n
  induction m using Quotient.ind; induction n using Quotient.ind
  rename_i xs ys
  show min x (Bag.mk (xs ++ ys)) = _
  rw [show Bag.mk (xs ++ ys) = Bag.mk (ys ++ xs) from Quotient.sound List.perm_append_comm]
  show List.foldr _ x (ys ++ xs) = _
  rw [List.foldr_append]; rfl

-- a value read within a list occurs in it, and a value read at one of the keys among the values read there
theorem count_earlier {α : Type} [Inhabited α] (xs : List α) :
    ∀ (j : Int), 0 ≤ j → j < xs.length → 1 ≤ N.count (earlier j xs) xs := by
  induction xs with
  | nil => intro j h0 h1; simp at h1; omega
  | cons x ys ih =>
    intro j h0 h1
    simp only [earlier, if_neg (show ¬j < 0 by omega)]
    by_cases e : j = 0
    · have := N.count_nonnegative x ys
      rw [if_pos e, N.count, if_pos rfl]; omega
    · rw [if_neg e, N.count]
      have := ih (j - 1) (by omega) (by simp at h1; omega)
      split <;> omega

theorem count_select {β : Type} [Inhabited β] (a : Int → β) (k : Int) (keys : List Int) (h : occurs k keys) :
    1 ≤ N.count (a k) (selects a keys) := by
  induction keys with
  | nil => exact absurd h (by simp [occurs])
  | cons y ys ih =>
    show 1 ≤ N.count (a k) (a y :: selects a ys)
    have hn := N.count_nonnegative (a k) (selects a ys)
    rw [N.count]
    rcases h with e | h
    · subst e; rw [if_pos rfl]; omega
    · have := ih h; split <;> omega

-- a single element is a submultiset if its multiplicity is positive
theorem single_le {α : Type} [Inhabited α] (v : α) (xs : List α) (h : 1 ≤ N.count v xs) : {v} ≤ Bag.mk xs := by
  intro e
  show Bag.count (Bag.mk [v]) e ≤ Bag.count (Bag.mk xs) e
  rw [count_mk, count_mk, N.count, N.count]
  have := N.count_nonnegative e xs
  by_cases ev : v = e
  · subst ev; rw [if_pos rfl]; omega
  · rw [if_neg ev]; omega

theorem single_earlier_le_elems : Stmt.single_earlier_le_elems := by
  intro α _ j xs ⟨h0, h1⟩
  rw [elems_mk]; exact iff_true_intro (single_le _ _ (count_earlier xs j h0 h1))

theorem single_select_le_elems : Stmt.single_select_le_elems := by
  intro a k keys n hkeys h
  rw [elems_mk]; exact iff_true_intro (single_le _ _ (count_select a k keys h))

theorem sum_consts : Stmt.sum_consts := by
  intro n x hn; simp only [sum_N] at *; rw [consts_N, N.sum_consts, N.integer_cast, Int.toNat_of_nonneg hn]

theorem sum_counter : Stmt.sum_counter := by
  intro i c n hn; simp only [sum_N] at *; rw [counter_N, N.sum_counter, N.integer_cast, Int.toNat_of_nonneg hn]

theorem counts_false : Stmt.counts_false := by
  intro x bs n hbs; exact N.counts_false x bs bs.length rfl

theorem counts_true : Stmt.counts_true := by
  intro x bs n hbs; exact N.counts_true x bs bs.length rfl

theorem current_trace_step_or_keep : Stmt.current_trace_step_or_keep := by
  intro x0 n a xs C hxs; simp only [count_N] at *
  rw [counter_N]
  exact N.current_trace_step_or_keep_gen a C _ xs x0 (by rw [N.length_butlast_counter]; omega)

theorem current_trace_add_at : Stmt.current_trace_add_at := by
  intro α _ a k values n hvalues; simp only [sum_N] at *; exact N.current_trace_add_at a k values values.length rfl

theorem current_trace_histogram : Stmt.current_trace_histogram := by
  intro c0 a n hs v hhs; simp only [count_N] at *; rw [counter_N]
  exact N.current_trace_histogram c0 a n.toNat hs v (by omega)

theorem current_counts : Stmt.current_counts := by
  intro α _ x e vs n hvs; simp only [count_N] at *; exact N.current_counts x e vs vs.length rfl

theorem earlier_counts : Stmt.earlier_counts := by
  intro α _ j x e vs n hvs ⟨hj, hjn⟩; simp only [count_N] at *
  rw [earlier_N_nonneg j _ hj, prefix_N]
  exact N.earlier_counts j.toNat x e vs n.toNat (by omega) (by rw [N.integer_cast, N.integer_cast]; omega)

theorem prefix_counts : Stmt.prefix_counts := by
  intro α _ k x e vs n hvs; exact prefix_trace_int k x vs _

-- a store at a key that is not among the keys leaves their selects unchanged
theorem selects_update_not_occurs {α β : Type} [Inhabited α] [Inhabited β] (a : α → β) (k : α) (v : β)
    (keys : List α) (h : ¬occurs k keys) : selects (fun j => if j = k then v else a j) keys = selects a keys := by
  induction keys with
  | nil => rfl
  | cons y ys ih =>
    simp only [occurs, not_or] at h
    simp only [selects, maps] at ih ⊢
    rw [ih h.2, if_neg h.1]

-- the selects after a store at one of distinct keys: the stored value in place of the old one, the rest unchanged; the
-- aggregates are folds of an operation g over the values from a neutral element z
theorem fold_selects_update {α β : Type} [Inhabited α] [Inhabited β] (z : Int) (g : β → Int) (agg : List β → Int)
    (hnil : agg [] = z) (hcons : ∀ v vs, agg (v :: vs) = g v + agg vs)
    (a : α → β) (k : α) (v : β) (keys : List α) (hd : distincts keys) :
    agg (selects (fun j => if j = k then v else a j) keys)
      = if occurs k keys then agg (selects a keys) + g v - g (a k) else agg (selects a keys) := by
  induction keys with
  | nil => rw [if_neg (by simp [occurs])]; rfl
  | cons y ys ih =>
    simp only [distincts] at hd
    have hs : ∀ (f : α → β), selects f (y :: ys) = f y :: selects f ys := fun f => rfl
    rw [hs, hs, hcons, hcons]
    by_cases e : y = k
    · subst e
      rw [if_pos (show occurs y (y :: ys) from Or.inl rfl), if_pos rfl, selects_update_not_occurs a y v ys hd.1]
      omega
    · have ho : occurs k (y :: ys) ↔ occurs k ys := by simp only [occurs]; exact ⟨fun h => h.resolve_left e, Or.inr⟩
      rw [if_neg e, ite_iff ho, ih hd.2]
      split <;> omega

theorem sum_selects_update : Stmt.sum_selects_update := by
  unfold Stmt.sum_selects_update; choices
  intro α _ a k v keys n hkeys hd; simp only [sum_N]
  exact fold_selects_update 0 id N.sum rfl (fun _ _ => rfl) a k v keys hd

theorem parity_selects_update : Stmt.parity_selects_update := by
  unfold Stmt.parity_selects_update; choices
  intro α _ a k v keys n hkeys hd; simp only [parity_N]
  exact fold_selects_update 0 (fun w => if w % 2 = 0 then 1 else -1) N.parity rfl (fun _ _ => rfl) a k v keys hd

theorem count_selects_update : Stmt.count_selects_update := by
  unfold Stmt.count_selects_update; choices
  intro α β _ _ a k w e keys n hkeys hd; simp only [count_N]
  exact fold_selects_update 0 (fun u => if u = e then 1 else 0) (N.count e) rfl (fun _ _ => rfl) a k w keys hd


-- the lengths of the folds of aggregation.dfy
theorem length_sums : Stmt.length_sums := by
  intro x values n hvalues; rw [sums, N.length_butlast_trace]

theorem length_maxs : Stmt.length_maxs := by
  intro x values n hvalues; rw [maxs, N.length_butlast_trace]

theorem length_mins : Stmt.length_mins := by
  intro x values n hvalues; rw [mins, N.length_butlast_trace]

theorem length_counts : Stmt.length_counts := by
  intro α _ x e vs n hvs; rw [counts, N.length_butlast_trace]

theorem length_compacts : Stmt.length_compacts := by
  intro c0 ks P n hks
  rw [compacts, N.length_butlast_trace, counts, N.length_zip_eq ks _ ks.length rfl]
  rw [N.length_butlast_trace, N.length_maps]

theorem length_filters_above : Stmt.length_filters_above := by
  intro c0 ks b F n hks
  rw [filters_above, N.length_butlast_trace, counts, N.length_zip_eq ks _ ks.length rfl]
  rw [N.length_butlast_trace, N.length_maps]

theorem length_filters_below : Stmt.length_filters_below := by
  intro c0 ks b F n hks
  rw [filters_below, N.length_butlast_trace, counts, N.length_zip_eq ks _ ks.length rfl]
  rw [N.length_butlast_trace, N.length_maps]

theorem length_parities : Stmt.length_parities := by
  intro x values n hvalues; rw [parities, N.length_butlast_trace]

theorem sums_consts : Stmt.sums_consts := by
  intro x n c; rw [consts_N, counter_N]; exact N.sums_consts x n.toNat c

-- the bounds of a sum by bounds of its elements, scaled by n: n times the sum of the list is bounded by its length
-- times the bound
theorem sum_scaled_above {β : Type} (e n : Int) (V : β → Int) : ∀ (ds : List β),
    invs ds (fun d => e ≤ n * V d) → (ds.length : Int) * e ≤ n * N.sum (maps ds V)
  | [], _ => by simp [maps, N.sum]
  | d :: ds, ⟨h, hs⟩ => by
    have ih := sum_scaled_above e n V ds hs
    simp only [maps, N.sum, List.length_cons, Int.natCast_add, Int.add_mul, Int.mul_add] at ih ⊢; omega

theorem sum_scaled_below {β : Type} (e n : Int) (V : β → Int) : ∀ (ds : List β),
    invs ds (fun d => n * V d ≤ e) → n * N.sum (maps ds V) ≤ (ds.length : Int) * e
  | [], _ => by simp [maps, N.sum]
  | d :: ds, ⟨h, hs⟩ => by
    have ih := sum_scaled_below e n V ds hs
    simp only [maps, N.sum, List.length_cons, Int.natCast_add, Int.add_mul, Int.mul_add] at ih ⊢; omega

-- for no iteration, the sum is 0, which the bound e ≤ 0 or 0 ≤ e decides
theorem sum_above : Stmt.sum_above := by
  intro n hs V e hhs ⟨hn, h⟩
  rw [sum_N]
  by_cases hp : 0 < n
  · have hl : ((List.zip (butlast (counter 0 1 n)) hs).length : Int) = n := by
      rw [counter_N, N.length_zip_eq _ hs n.toNat (N.length_butlast_counter 0 1 n.toNat) (by omega)]; omega
    have hb := sum_scaled_above e n (fun (⟨k, h⟩ : Int × Int) => V k h) _ h
    rw [hl] at hb
    exact Int.le_of_mul_le_mul_left (a := n) hb hp
  · rw [counter_N, show n.toNat = 0 by omega]; simp [N.counter, butlast, maps, N.sum]; omega

theorem sum_below : Stmt.sum_below := by
  intro n hs V e hhs ⟨hn, h⟩
  rw [sum_N]
  by_cases hp : 0 < n
  · have hl : ((List.zip (butlast (counter 0 1 n)) hs).length : Int) = n := by
      rw [counter_N, N.length_zip_eq _ hs n.toNat (N.length_butlast_counter 0 1 n.toNat) (by omega)]; omega
    have hb := sum_scaled_below e n (fun (⟨k, h⟩ : Int × Int) => V k h) _ h
    rw [hl] at hb
    exact Int.le_of_mul_le_mul_left (a := n) hb hp
  · rw [counter_N, show n.toNat = 0 by omega]; simp [N.counter, butlast, maps, N.sum]; omega

theorem sum_mod_below : Stmt.sum_mod_below := by
  unfold Stmt.sum_mod_below; choices
  intro n m e ⟨hn, h⟩; simp only [sum_N] at *
  rw [counter_N]; apply N.sum_mod_below n.toNat m e; rw [N.integer_cast, Int.toNat_of_nonneg hn]; exact h

theorem sum_neg : Stmt.sum_neg := by
  intro values n hvalues; simp only [sum_N] at *; exact N.sum_neg values values.length rfl

theorem sum_scale : Stmt.sum_scale := by
  intro values a n hvalues; simp only [sum_N] at *; exact N.sum_scale values a values.length rfl

theorem sum_add : Stmt.sum_add := by
  intro xs ys n hxs hys; simp only [sum_N] at *; exact N.sum_add xs ys xs.length rfl (by omega)

theorem sum_indicator_true : Stmt.sum_indicator_true := by
  unfold Stmt.sum_indicator_true; choices
  intro α _ xs P n hxs; simp only [sum_N, count_N] at *; exact N.sum_indicator_true xs P xs.length rfl

theorem sum_indicator_false : Stmt.sum_indicator_false := by
  unfold Stmt.sum_indicator_false; choices
  intro α _ xs P n hxs; simp only [sum_N, count_N] at *; exact N.sum_indicator_false xs P xs.length rfl

-- a sum of multiples of m is one: the remainder of a sum is that of the sum of the remainders
theorem sum_mod_multiples_list {β : Type} (m : Int) (V : β → Int) : ∀ (ds : List β),
    invs ds (fun d => V d % m = 0) → N.sum (maps ds V) % m = 0
  | [], _ => by simp [maps, N.sum]
  | d :: ds, ⟨h, hs⟩ => by
    have ih := sum_mod_multiples_list m V ds hs
    simp only [maps, N.sum]; rw [Int.add_emod, h, ih]; rfl

theorem sum_mod_multiples : Stmt.sum_mod_multiples := by
  intro n hs V m hhs ⟨hm, h⟩
  rw [sum_N]; exact sum_mod_multiples_list m (fun (⟨k, h⟩ : Int × Int) => V k h) _ h

theorem sum_parity_indicator : Stmt.sum_parity_indicator := by
  unfold Stmt.sum_parity_indicator; choices
  intro α _ xs F n hxs; rw [sum_N, parity_N]; clear hxs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [maps, N.sum, N.parity]; rw [ih]

theorem count_consts : Stmt.count_consts := by
  unfold Stmt.count_consts; choices
  intro α _ n e v hn; simp only [count_N] at *; rw [consts_N, N.count_consts, N.integer_cast, Int.toNat_of_nonneg hn]

theorem count_true_below : Stmt.count_true_below := by
  intro m i n h; simp only [count_N] at *
  rw [counter_N]; exact N.count_true_below m i n.toNat (by rw [N.integer_cast]; omega)

theorem count_true_above : Stmt.count_true_above := by
  intro m i n h; simp only [count_N] at *
  rw [counter_N, N.count_true_above m i n.toNat (by rw [N.integer_cast]; omega), N.integer_cast]; omega

theorem count_nonnegative : Stmt.count_nonnegative := by
  intro α _ e vs; rw [count_N]; exact N.count_nonnegative e vs

theorem count_remainder : Stmt.count_remainder := by
  intro n m r ⟨hn, h⟩; simp only [count_N] at *
  rw [counter_N, N.count_remainder n.toNat m r h, N.integer_cast, Int.toNat_of_nonneg hn]

theorem count_false_true : Stmt.count_false_true := by
  intro i c n hs P hhs hn; simp only [count_N] at *
  rw [counter_N, N.count_false_true i c n.toNat hs P (by omega), N.integer_cast, Int.toNat_of_nonneg hn]

theorem count_true_eq : Stmt.count_true_eq := by
  intro ks r hs F n hks hhs; simp only [count_N] at *; exact N.count_true_eq ks r hs F ks.length rfl (by omega)

-- the final value of a trace is the left fold of its update over the dependency
theorem current_trace_foldl {α β : Type} [Inhabited α] (x : α) (vs : List β) (f : α → β → α) :
    current (trace x vs f) = vs.foldl f x := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih => exact ih (f x v)

-- the prefix maxima and minima end in the maximum and the minimum of the multiset: their update is that of the fold
-- of max and min, and the left fold is the right one over the reversed list, a permutation
theorem maxs_max (x : Int) (values : List Int) : current (maxs x values) = max x (elems values) := by
  have hf : (fun m v => if m < v then v else if v ≤ m then m else unspecified)
      = (fun m v : Int => if m ≤ v then v else m) := by
    funext m v; by_cases h : m < v
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_pos (by omega)]; by_cases e : m = v
      · rw [if_pos (by omega), e]
      · rw [if_neg (by omega)]
  rw [maxs, current_trace_foldl, hf, List.foldl_eq_foldr_reverse, elems_mk,
    show Bag.mk values = Bag.mk values.reverse from Quotient.sound (List.reverse_perm values).symm]
  rfl

theorem mins_min (x : Int) (values : List Int) : current (mins x values) = min x (elems values) := by
  have hf : (fun m v => if v < m then v else if m ≤ v then m else unspecified)
      = (fun m v : Int => if m ≤ v then m else v) := by
    funext m v; by_cases h : v < m
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg h, if_pos (by omega), if_pos (by omega)]
  rw [mins, current_trace_foldl, hf, List.foldl_eq_foldr_reverse, elems_mk,
    show Bag.mk values = Bag.mk values.reverse from Quotient.sound (List.reverse_perm values).symm]
  rfl

theorem current_maxs : Stmt.current_maxs := by
  intro x values n hvalues; exact maxs_max x values

theorem current_mins : Stmt.current_mins := by
  intro x values n hvalues; exact mins_min x values

theorem earlier_maxs : Stmt.earlier_maxs := by
  intro j x values n hvalues ⟨hj, hjn⟩
  rw [maxs, earlier_trace_int j _ _ _ hj (by omega)]; exact maxs_max x _

theorem prefix_maxs : Stmt.prefix_maxs := by
  intro k x values n hvalues; exact prefix_trace_int k x values _

theorem earlier_mins : Stmt.earlier_mins := by
  intro j x values n hvalues ⟨hj, hjn⟩
  rw [mins, earlier_trace_int j _ _ _ hj (by omega)]; exact mins_min x _

theorem prefix_mins : Stmt.prefix_mins := by
  intro k x values n hvalues; exact prefix_trace_int k x values _

theorem max_initial : Stmt.max_initial := by
  intro x values; rw [← maxs_max]; exact N.current_maxs_initial x values values.length rfl

theorem max_earlier : Stmt.max_earlier := by
  intro k x values ⟨hk, hkn⟩
  rw [← maxs_max, earlier_N_nonneg k _ hk]
  exact N.current_maxs_earlier k.toNat x values values.length rfl (by rw [N.integer_cast, N.integer_cast]; omega)

-- a position below the cut and within the list is within the prefix
theorem lt_length_prefix {α : Type} [Inhabited α] (k n : Nat) (xs : List α) (hn : k < n) (hxs : k < xs.length) :
    k < (N.«prefix» n xs).length := by
  induction xs generalizing k n with
  | nil => simp at hxs
  | cons x ys ih =>
    cases n with
    | zero => omega
    | succ m =>
      simp only [N.«prefix», List.length_cons]
      cases k with
      | zero => omega
      | succ j => have := ih j m (by omega) (by simp at hxs; omega); omega

theorem max_prefix_earlier : Stmt.max_prefix_earlier := by
  intro k x n xs hxs ⟨hk, hkn⟩
  rw [← earlier_prefix k n xs hkn]
  exact max_earlier k x («prefix» n xs)
    ⟨hk, by rw [prefix_N]; have := lt_length_prefix k.toNat n.toNat xs (by omega) (by omega); omega⟩

theorem min_initial : Stmt.min_initial := by
  intro x values; rw [← mins_min]; exact N.current_mins_initial x values values.length rfl

theorem min_earlier : Stmt.min_earlier := by
  intro k x values ⟨hk, hkn⟩
  rw [← mins_min, earlier_N_nonneg k _ hk]
  exact N.current_mins_earlier k.toNat x values values.length rfl (by rw [N.integer_cast, N.integer_cast]; omega)

theorem min_prefix_earlier : Stmt.min_prefix_earlier := by
  intro k x n xs hxs ⟨hk, hkn⟩
  rw [← earlier_prefix k n xs hkn]
  exact min_earlier k x («prefix» n xs)
    ⟨hk, by rw [prefix_N]; have := lt_length_prefix k.toNat n.toNat xs (by omega) (by omega); omega⟩

theorem max_seeded_earlier : Stmt.max_seeded_earlier := by
  intro j h i n xs ⟨hh, hj1, hj2⟩
  rw [← maxs_max]
  by_cases e : j = h
  · subst e; exact N.current_maxs_initial _ _ _ rfl
  · rw [counter_N]
    have hr := N.current_maxs_earlier (j - i).toNat (earlier h xs)
      (maps (butlast (N.counter i 1 n.toNat)) (fun v => earlier v xs)) n.toNat
      (by rw [N.length_maps, N.length_butlast_counter]) (by rw [N.integer_cast, N.integer_cast]; omega)
    rwa [N.earlier_maps_counter _ _ _ _ (by omega), show i + ((j - i).toNat : Int) = j by omega] at hr

theorem min_seeded_earlier : Stmt.min_seeded_earlier := by
  intro j h i n xs ⟨hh, hj1, hj2⟩
  rw [← mins_min]
  by_cases e : j = h
  · subst e; exact N.current_mins_initial _ _ _ rfl
  · rw [counter_N]
    have hr := N.current_mins_earlier (j - i).toNat (earlier h xs)
      (maps (butlast (N.counter i 1 n.toNat)) (fun v => earlier v xs)) n.toNat
      (by rw [N.length_maps, N.length_butlast_counter]) (by rw [N.integer_cast, N.integer_cast]; omega)
    rwa [N.earlier_maps_counter _ _ _ _ (by omega), show i + ((j - i).toNat : Int) = j by omega] at hr

-- the bitwise aggregates: band and bor are the folds of bitand from all ones and of bitor from zero, operations that
-- are associative and commutative with these neutral elements, hence a fold from any value is the operation of the
-- value and the aggregate
theorem foldr_neutral (op : Int → Int → Int) (z : Int) (assoc : ∀ a b c, op (op a b) c = op a (op b c))
    (neutral : ∀ a, op z a = a) (xs : List Int) (y : Int) : xs.foldr op y = op (xs.foldr op z) y := by
  induction xs with
  | nil => exact (neutral y).symm
  | cons x xs ih => simp only [List.foldr_cons]; rw [ih, assoc]

theorem foldl_neutral (op : Int → Int → Int) (z : Int) (assoc : ∀ a b c, op (op a b) c = op a (op b c))
    (neutral : ∀ a, op a z = a) (xs : List Int) (x : Int) : xs.foldl op x = op x (xs.foldr op z) := by
  induction xs generalizing x with
  | nil => exact (neutral x).symm
  | cons v vs ih => simp only [List.foldl_cons, List.foldr_cons]; rw [ih, assoc]

theorem band_N (xs : List Int) : band (elems xs) = xs.foldr bitand (-1) := by rw [elems_mk]; rfl

theorem bor_N (xs : List Int) : bor (elems xs) = xs.foldr bitor 0 := by rw [elems_mk]; rfl

theorem bitand_assoc (a b c : Int) : bitand (bitand a b) c = bitand a (bitand b c) := Bits.land_assoc a b c

theorem bitor_assoc (a b c : Int) : bitor (bitor a b) c = bitor a (bitor b c) := Bits.lor_assoc a b c

theorem bitand_neg_one (a : Int) : bitand a (-1) = a := Bits.land_neg_one a

theorem neg_one_bitand (a : Int) : bitand (-1) a = a := by
  show Bits.land (-1) a = a; rw [Bits.land_comm]; exact Bits.land_neg_one a

theorem bitor_zero (a : Int) : bitor a 0 = a := Bits.lor_zero a

theorem zero_bitor (a : Int) : bitor 0 a = a := by
  show Bits.lor 0 a = a; rw [Bits.lor_comm]; exact Bits.lor_zero a

theorem band_empty : Stmt.band_empty := rfl

theorem band_single : Stmt.band_single := fun x => bitand_neg_one x

theorem band_union : Stmt.band_union := by
  intro m n
  induction m using Quotient.ind; induction n using Quotient.ind
  rename_i xs ys
  show (xs ++ ys).foldr bitand (-1) = bitand (xs.foldr bitand (-1)) (ys.foldr bitand (-1))
  rw [List.foldr_append]; exact foldr_neutral bitand (-1) bitand_assoc neg_one_bitand xs _

theorem bor_empty : Stmt.bor_empty := rfl

theorem bor_single : Stmt.bor_single := fun x => bitor_zero x

theorem bor_union : Stmt.bor_union := by
  intro m n
  induction m using Quotient.ind; induction n using Quotient.ind
  rename_i xs ys
  show (xs ++ ys).foldr bitor 0 = bitor (xs.foldr bitor 0) (ys.foldr bitor 0)
  rw [List.foldr_append]; exact foldr_neutral bitor 0 bitor_assoc zero_bitor xs _

theorem length_bands : Stmt.length_bands := by
  intro x values n hvalues; rw [bands, N.length_butlast_trace]

theorem current_bands : Stmt.current_bands := by
  intro x values n hvalues
  rw [bands, current_trace_foldl, band_N]; exact foldl_neutral bitand (-1) bitand_assoc bitand_neg_one values x

theorem earlier_bands : Stmt.earlier_bands := by
  intro j x values n hvalues ⟨hj, hjn⟩
  rw [bands, earlier_trace_int j _ _ _ hj (by omega), current_trace_foldl, band_N]
  exact foldl_neutral bitand (-1) bitand_assoc bitand_neg_one _ x

theorem length_bors : Stmt.length_bors := by
  intro x values n hvalues; rw [bors, N.length_butlast_trace]

theorem current_bors : Stmt.current_bors := by
  intro x values n hvalues
  rw [bors, current_trace_foldl, bor_N]; exact foldl_neutral bitor 0 bitor_assoc bitor_zero values x

theorem earlier_bors : Stmt.earlier_bors := by
  intro j x values n hvalues ⟨hj, hjn⟩
  rw [bors, earlier_trace_int j _ _ _ hj (by omega), current_trace_foldl, bor_N]
  exact foldl_neutral bitor 0 bitor_assoc bitor_zero _ x

-- the seeds: the counter from q - 1 is the counter from q after q - 1, and the reads of the list at k + 1 those of its
-- tail at k, which are its prefix
theorem counter_pred (q n : Int) (hn : 0 ≤ n) : counter (q - 1) 1 (n + 1) = .step (q - 1) (counter q 1 n) := by
  rw [counter, if_neg (by omega), show q - 1 + 1 = q by omega, show n + 1 - 1 = n by omega]

theorem maps_earlier_succ (x : Int) (xs : List Int) (n : Int) (hxs : n ≤ length xs) :
    maps (butlast (counter 0 1 n)) (fun k => earlier (k + 1) (x :: xs)) = «prefix» n xs := by
  rw [← maps_earlier n xs hxs, counter_N]
  exact N.maps_counter_congr_gen 0 n.toNat _ _ (fun k hk => by
    simp only [earlier, show ¬k + 1 < 0 by omega, show k + 1 ≠ 0 by omega, if_false, Int.add_sub_cancel])

theorem prefix_succ {α : Type} [Inhabited α] (x : α) (xs : List α) (n : Int) (hn : 0 ≤ n) :
    «prefix» (n + 1) (x :: xs) = x :: «prefix» n xs := by
  simp only [«prefix», show ¬n + 1 ≤ 0 by omega, if_false, Int.add_sub_cancel]

theorem band_seed_selects : Stmt.band_seed_selects := by
  intro a q n v ⟨hn, hv⟩; subst hv
  rw [counter_pred q n hn, band_N, band_N]; rfl

theorem bor_seed_selects : Stmt.bor_seed_selects := by
  intro a q n v ⟨hn, hv⟩; subst hv
  rw [counter_pred q n hn, bor_N, bor_N]; rfl

theorem band_seed_earlier : Stmt.band_seed_earlier := by
  intro xs n hxs hn
  cases xs with
  | nil => simp at hxs; omega
  | cons x xs =>
    rw [maps_earlier_succ x xs n (by simp at hxs; omega), prefix_succ x xs n hn, band_N, band_N]; rfl

theorem bor_seed_earlier : Stmt.bor_seed_earlier := by
  intro xs n hxs hn
  cases xs with
  | nil => simp at hxs; omega
  | cons x xs =>
    rw [maps_earlier_succ x xs n (by simp at hxs; omega), prefix_succ x xs n hn, bor_N, bor_N]; rfl

-- compacts without the dead branch of its update, from the count 0 on
theorem compacts_N (c0 : Int → Int) (ks : List Int) (P : Int → Prop) : compacts c0 ks P = N.compacting P c0 0 ks := by
  simp only [compacts, N.compacting, N.ite_not_else]

theorem select_current_compacts_lower : Stmt.select_current_compacts_lower := by
  intro c0 K n m x P ⟨hK, hm, hx0, hxm⟩; simp only [count_N] at *
  subst hK hm
  rw [counter_N] at hxm ⊢
  rw [compacts_N]
  have := (N.compacting_from P n.toNat 0 0 c0 x).2.2 ⟨hx0, by omega⟩
  omega

theorem select_current_compacts_upper : Stmt.select_current_compacts_upper := by
  intro c0 K n m x P ⟨hK, hm, hx0, hxm⟩; simp only [count_N] at *
  subst hK hm
  rw [counter_N] at hxm ⊢
  rw [compacts_N]
  have h1 := (N.compacting_from P n.toNat 0 0 c0 x).1
  have := (N.compacting_from P n.toNat 0 0 c0 x).2.2 ⟨hx0, by omega⟩
  omega

theorem select_current_filters_above : Stmt.select_current_filters_above := by
  intro c0 ks b F m x n hks ⟨hm, hx0, hxm⟩; simp only [count_N] at *
  rw [show filters_above c0 ks b F = N.filtering_above c0 0 ks b F by
    simp only [filters_above, N.filtering_above, N.ite_le_lt]]
  exact (N.filtering_above_from b F ks 0 c0 x).2 ⟨hx0, by omega⟩

theorem select_current_filters_below : Stmt.select_current_filters_below := by
  intro c0 K n b F m x ⟨hK, hm, hx0, hxm⟩; simp only [count_N] at *
  subst hK
  rw [counter_N] at hm ⊢
  rw [show filters_below c0 (butlast (N.counter 0 1 n.toNat)) b F
      = N.filtering_below c0 0 (butlast (N.counter 0 1 n.toNat)) b F by
    simp only [filters_below, N.filtering_below, N.ite_le_lt]]
  have ht := N.count_true_false (fun k => b ≤ F k) (butlast (N.counter 0 1 n.toNat))
  rw [N.length_butlast_counter] at ht
  have h1 := N.count_nonnegative True (maps (butlast (N.counter 0 1 n.toNat)) (fun k => b ≤ F k))
  have h2 := N.count_nonnegative False (maps (butlast (N.counter 0 1 n.toNat)) (fun k => b ≤ F k))
  exact (N.filtering_below_from b F _ 0 c0 x).2 ⟨hx0, by omega⟩

theorem current_parities : Stmt.current_parities := by
  intro x values n hvalues; simp only [parity_N] at *; exact N.current_parities x values values.length rfl

theorem earlier_parities : Stmt.earlier_parities := by
  intro j x values n hvalues ⟨hj, hjn⟩
  rw [parities, earlier_trace_int j _ _ _ hj (by omega)]; exact current_parities x _ _ rfl

theorem prefix_parities : Stmt.prefix_parities := by
  intro k x values n hvalues; exact prefix_trace_int k x values _

theorem select_current_trace_reset_add : Stmt.select_current_trace_reset_add := by
  unfold Stmt.select_current_trace_reset_add; choices
  intro a0 j n c G
  rw [sum_N, counter_N, N.select_current_trace_reset_add]
  exact ite_iff (by show n.toNat = 0 ↔ _; omega) _ _

-- the reset and the guarded additions: after the reset at the iteration 0, each later iteration adds G k where P k holds
-- and keeps the array otherwise
theorem reset_add_keep_later (j c : Int) (P : Int → Prop) (G : Int → Int) (m : Nat) : ∀ (s : Int) (x : Int → Int), 1 ≤ s →
    current (trace x (butlast (N.counter s 1 m))
      (fun a k =>
        if k = 0 then fun j1 => if j1 = j then c else a j1
        else if 0 < k ∧ P k then fun j1 => if j1 = j then a j + G k else a j1
        else if 0 < k ∧ ¬P k then a else unspecified)) j
      = x j + N.sum (maps (butlast (N.counter s 1 m)) (fun k => if 0 < k ∧ P k then G k else 0)) := by
  induction m with
  | zero => intro s x hs; simp [N.counter, butlast, trace, current, maps, N.sum]
  | succ m ih =>
    intro s x hs
    rw [N.butlast_counter_succ, N.trace_cons, N.current_step_eq, ih (s + 1) _ (by omega)]
    simp only [maps, N.sum, if_neg (show ¬s = 0 by omega)]
    by_cases hp : P s
    · simp only [hp, and_true, not_true_eq_false, and_false, if_pos (show 0 < s by omega), ↓reduceIte, eq_self]; omega
    · simp only [hp, and_true, not_false_eq_true, and_false, if_pos (show 0 < s by omega), ↓reduceIte]; omega

theorem select_current_trace_reset_add_keep : Stmt.select_current_trace_reset_add_keep := by
  intro a0 j n c P G
  conv => rhs; simp (disch := complement) only [cases_of]
  rw [counter_N, sum_N]
  by_cases hn : n ≤ 0
  · rw [if_pos hn, show n.toNat = 0 by omega]; rfl
  · rw [if_neg hn, show n.toNat = n.toNat - 1 + 1 by omega, N.butlast_counter_succ, N.trace_cons, N.current_step_eq,
      reset_add_keep_later j c P G _ (0 + 1) _ (by omega)]
    simp only [maps, N.sum, ↓reduceIte, Int.lt_irrefl, false_and]
    omega

-- the same for a value instead of an array
theorem reset_add_keep_later_value (c : Int) (P : Int → Prop) (G : Int → Int) (m : Nat) : ∀ (s : Int) (x : Int), 1 ≤ s →
    current (trace x (butlast (N.counter s 1 m))
      (fun x k => if k = 0 then c else if 0 < k ∧ P k then x + G k else if 0 < k ∧ ¬P k then x else unspecified))
      = x + N.sum (maps (butlast (N.counter s 1 m)) (fun k => if 0 < k ∧ P k then G k else 0)) := by
  induction m with
  | zero => intro s x hs; simp [N.counter, butlast, trace, current, maps, N.sum]
  | succ m ih =>
    intro s x hs
    rw [N.butlast_counter_succ, N.trace_cons, N.current_step_eq, ih (s + 1) _ (by omega)]
    simp only [maps, N.sum, if_neg (show ¬s = 0 by omega)]
    by_cases hp : P s
    · simp only [hp, and_true, not_true_eq_false, and_false, if_pos (show 0 < s by omega), ↓reduceIte]; omega
    · simp only [hp, and_true, not_false_eq_true, and_false, if_pos (show 0 < s by omega), ↓reduceIte]; omega

theorem current_trace_reset_add_keep : Stmt.current_trace_reset_add_keep := by
  intro x0 n c P G
  conv => rhs; simp (disch := complement) only [cases_of]
  rw [counter_N, sum_N]
  by_cases hn : n ≤ 0
  · rw [if_pos hn, show n.toNat = 0 by omega]; rfl
  · rw [if_neg hn, show n.toNat = n.toNat - 1 + 1 by omega, N.butlast_counter_succ, N.trace_cons, N.current_step_eq,
      reset_add_keep_later_value c P G _ (0 + 1) _ (by omega)]
    simp only [maps, N.sum, ↓reduceIte, Int.lt_irrefl, false_and]
    omega

theorem length_scans : Stmt.length_scans := by
  intro a keys values n hkeys hvalues
  rw [scans, N.length_butlast_trace, N.length_zip_eq keys values keys.length rfl (by omega)]

theorem earlier_scans : Stmt.earlier_scans := by
  intro j a keys values n hkeys hvalues ⟨hj, hjn⟩
  rw [scans, scans, earlier_trace_int j _ _ _ hj
    (by rw [N.length_zip_eq keys values keys.length rfl (by omega)]; omega), prefix_zip_int]

theorem prefix_scans : Stmt.prefix_scans := by
  intro k a keys values n hkeys hvalues; rw [scans, scans, prefix_trace_int, prefix_zip_int]

-- the scan over i, ..., i + m - 1 stores at i + 1, ..., i + m the value at i plus the sums of the values so far
theorem select_current_scans_N (m : Nat) : ∀ (b0 : Int → Int) (i : Int) (values : List Int) (j : Int),
    values.length = m → current (scans b0 (butlast (N.counter i 1 m)) values) j
      = if i ≤ j ∧ j ≤ i + m then b0 i + N.sum («prefix» (j - i) values) else b0 j := by
  induction m with
  | zero =>
    intro b0 i values j h
    rw [List.length_eq_zero_iff.1 h]
    show b0 j = _
    by_cases hj : i ≤ j ∧ j ≤ i + ((0 : Nat) : Int)
    · rw [if_pos hj, show j = i by omega]; simp [«prefix», N.sum]
    · rw [if_neg hj]
  | succ m ih =>
    intro b0 i values j h
    cases values with
    | nil => simp at h
    | cons v vs =>
      show current (scans (fun l => if l = i + 1 then b0 i + v else b0 l) (butlast (N.counter (i + 1) 1 m)) vs) j = _
      rw [ih _ (i + 1) vs j (by simpa using h)]
      by_cases h1 : i + 1 ≤ j ∧ j ≤ i + 1 + m
      · rw [if_pos h1, if_pos (by omega),
          show «prefix» (j - i) (v :: vs) = v :: «prefix» (j - (i + 1)) vs by
            simp only [«prefix»]; rw [if_neg (by omega), show j - i - 1 = j - (i + 1) by omega]]
        simp only [N.sum]; omega
      · rw [if_neg h1, if_neg (show ¬j = i + 1 by omega)]
        by_cases h2 : j = i
        · subst h2; rw [if_pos (by omega), Int.sub_self]; simp [«prefix», N.sum]
        · rw [if_neg (by omega)]

theorem select_current_scans : Stmt.select_current_scans := by
  intro b0 i n values j hvalues hn
  conv => rhs; simp (disch := complement) only [cases_of]
  rw [counter_N, select_current_scans_N n.toNat b0 i values j (by omega), sum_N, Int.toNat_of_nonneg hn]

theorem select_current_trace_recurrence : Stmt.select_current_trace_recurrence := by
  unfold Stmt.select_current_trace_recurrence; choices
  intro a0 n c j G
  rw [sum_N, counter_N, N.select_current_trace_recurrence, N.integer_cast, N.natural_eq, counter_N]
  exact ite_iff (by omega) _ _

-- the lemmas of arithmetic.dfy, which do not count

theorem mod_self : Stmt.mod_self := N.mod_self
theorem double_eq_half : Stmt.double_eq_half := N.double_eq_half
theorem div_below : Stmt.div_below := N.div_below
theorem div_nonpos : Stmt.div_nonpos := N.div_nonpos
theorem mul_lt_cancel : Stmt.mul_lt_cancel := N.mul_lt_cancel
theorem triangle_bound : Stmt.triangle_bound := N.triangle_bound
theorem triangle_nonneg : Stmt.triangle_nonneg := N.triangle_nonneg
theorem triangle_nonneg_below : Stmt.triangle_nonneg_below := N.triangle_nonneg_below
theorem triangle_even : Stmt.triangle_even := N.triangle_even
theorem triangle_even_below : Stmt.triangle_even_below := N.triangle_even_below
theorem triangle_even_scaled : Stmt.triangle_even_scaled := N.triangle_even_scaled
theorem triangle_even_below_scaled : Stmt.triangle_even_below_scaled := N.triangle_even_below_scaled

theorem pow_zero : Stmt.pow_zero := by
  intro c n hn; rw [pow_N, show n.toNat = 0 by omega]; rfl

theorem pow_one : Stmt.pow_one := by
  intro c; rw [pow_N]; simp [N.pow]

theorem square_eq_self : Stmt.square_eq_self := by
  intro c
  constructor
  · intro h
    have e : c * (c - 1) = 0 := by rw [Int.mul_sub, h]; omega
    rcases Int.mul_eq_zero.mp e with e | e <;> omega
  · rintro (e | e) <;> subst e <;> rfl

-- the lemmas of search.dfy

theorem not_occurs_prefix : Stmt.not_occurs_prefix := by
  intro n e xs hxs
  rw [counter_N, prefix_N, invs_counter_congr 0 n.toNat _ (fun k => N.earlier (N.natural k) xs ≠ e)
    (fun k hk => by rw [earlier_N_nonneg k xs hk, N.natural_eq])]
  exact N.not_occurs_prefix n.toNat e xs (by rw [N.integer_cast, N.integer_cast]; omega)

theorem invs_agree_prefix : Stmt.invs_agree_prefix := by
  intro n xs ys hxs hys
  rw [agree_prefix_N, N.agree_prefix_forall, prefix_N, prefix_N, N.prefix_eq_forall n.toNat xs ys (by omega) (by omega)]

theorem earlier_eq_prefix : Stmt.earlier_eq_prefix := by
  intro j n xs ys ⟨h, hj, hjn⟩
  rw [prefix_N, prefix_N] at h
  rw [earlier_N_nonneg j xs hj, earlier_N_nonneg j ys hj, iff_true]
  exact N.earlier_eq_prefix j.toNat n.toNat xs ys h (by omega)

theorem earlier_eq_not_occurs_prefix : Stmt.earlier_eq_not_occurs_prefix := by
  intro j n e xs hxs ⟨h, hj, hjn⟩
  rw [prefix_N] at h
  rw [earlier_N_nonneg j xs hj, iff_false]
  exact N.earlier_not_occurs_prefix n.toNat j.toNat e xs (by omega) ⟨h, by rw [N.integer_cast, N.integer_cast]; omega⟩

theorem earlier_above_iterations : Stmt.earlier_above_iterations := by
  intro j n ts n1 hts hn ⟨h, hj, hjn⟩
  rw [above_iterations_N] at h
  rw [earlier_N_nonneg j ts hj, iff_true]
  have := N.earlier_above_iterations n.toNat j.toNat ts n.toNat (by omega) rfl
    ⟨h, by rw [N.integer_cast, N.integer_cast]; omega⟩
  rw [N.integer_cast, Int.toNat_of_nonneg hj] at this
  exact this

theorem invs_select_store_ne : Stmt.invs_select_store_ne := by
  intro x a j i n
  rw [counter_N, N.invs_counter_forall, N.invs_counter_forall]
  constructor
  · intro h
    refine ⟨fun ⟨h1, h2⟩ => ?_, fun k hk => ?_⟩
    · have := h (j - i).toNat (by omega)
      rw [show i + ((j - i).toNat : Int) = j by omega] at this
      simp at this
    · have := h k hk
      by_cases e : i + k = j <;> simp_all
  · intro ⟨h1, h2⟩ k hk
    by_cases e : i + k = j
    · exact absurd ⟨by omega, by omega⟩ h1
    · simpa [e] using h2 k hk

theorem not_occurs_selects : Stmt.not_occurs_selects := by
  intro a x i n; rw [counter_N]; exact N.not_occurs_selects a x i n.toNat

theorem select_eq_not_occurs_selects : Stmt.select_eq_not_occurs_selects := by
  intro k a x i n ⟨h, h1, h2⟩
  rw [counter_N] at h
  rw [iff_false]
  exact N.select_not_occurs_selects a x i n.toNat k ⟨h, h1, by rw [N.integer_cast]; omega⟩

theorem bisection_lo : Stmt.bisection_lo := by
  intro l0 h0 ks M G H n hks h; rw [cut_N]; exact N.bisection_lo l0 h0 ks M G H ks.length rfl h

theorem bisection_hi : Stmt.bisection_hi := by
  intro l0 h0 ks M G H n hks h; rw [cut_N]; exact N.bisection_hi l0 h0 ks M G H ks.length rfl h

-- the lemmas of sorted.dfy

theorem sorted_empty : Stmt.sorted_empty := N.sorted_empty
theorem sorted_short : Stmt.sorted_short := N.sorted_short
theorem partitioned_empty : Stmt.partitioned_empty := N.partitioned_empty
theorem partitioned_whole : Stmt.partitioned_whole := N.partitioned_whole

theorem sorted_adjacent : Stmt.sorted_adjacent := by
  intro a n
  rw [counter_N, counter_N, N.sorted_adjacent, N.integer_cast]
  rcases Int.lt_or_le n 0 with hn | hn
  · rw [N.sorted_short a 0 _ (by omega), N.sorted_short a 0 _ (by omega)]
  · rw [Int.toNat_of_nonneg hn]

theorem perm_refl : Stmt.perm_refl := N.perm_refl
theorem select_swap : Stmt.select_swap := by
  intro a p q j
  show (if j = q then a p else if j = p then a q else a j) = _
  by_cases h1 : j = q
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : j = p
    · rw [if_pos h2, if_pos ⟨h1, h2⟩]
    · rw [if_neg h2, if_neg (fun h => h2 h.2), if_pos ⟨h1, h2⟩]

theorem perm_swap : Stmt.perm_swap := N.perm_swap

theorem perm_swaps : Stmt.perm_swaps := by
  intro a b ks hs P Q n hks hhs; exact N.perm_swaps a b ks hs P Q ks.length rfl (by omega)

theorem perm_steps_three : Stmt.perm_steps_three := by
  intro a c ks ns is F n _ _ _ hF
  exact N.perm_steps_general a c (List.zip ks (List.zip ns is)) _ (fun b ⟨k, nn, i⟩ => hF b k nn i)

-- a sort of no steps leaves the array as it is, which is sorted on the empty range
theorem sorted_prefix_steps : Stmt.sorted_prefix_steps := by
  intro a n m F ⟨hn, hF⟩
  rw [counter_N]
  rcases Int.lt_or_le m 0 with hm | hm
  · rw [show m.toNat = 0 by omega]; exact N.sorted_short _ 0 n (by omega)
  · exact N.sorted_prefix_steps a n m.toNat F ⟨by rw [N.integer_cast, Int.toNat_of_nonneg hm]; exact hn, hF⟩

theorem sorted_prefix_steps_two : Stmt.sorted_prefix_steps_two := by
  intro a n m F ⟨hn, hF⟩
  rw [counter_N, counter_N]
  rcases Int.lt_or_le m 0 with hm | hm
  · rw [show m.toNat = 0 by omega]; exact N.sorted_short _ 0 n (by omega)
  · exact N.sorted_prefix_steps_two a n m.toNat F ⟨by rw [N.integer_cast, Int.toNat_of_nonneg hm]; exact hn, hF⟩

theorem lower_rule : Stmt.lower_rule := by
  intro ar len y m h; rw [lower_N]; exact N.lower_rule ar len y m h

theorem upper_rule : Stmt.upper_rule := by
  intro ar len y m h; rw [upper_N]; exact N.upper_rule ar len y m h

theorem lower_le : Stmt.lower_le := by
  intro ar len y m h; rw [lower_N]; exact N.lower_le ar len y m h

theorem equal : Stmt.equal := by
  intro ar len y m h; rw [lower_N, upper_N]; exact N.equal ar len y m h

theorem bounds : Stmt.bounds := by
  intro ar len y h; rw [lower_N, upper_N]; exact N.bounds ar len y h

theorem cut_lower : Stmt.cut_lower := by
  intro ar len y h; rw [lower_N, cut_N]; exact N.cut_lower ar len y h

theorem lower_succ : Stmt.lower_succ := by
  intro ar len y h; rw [lower_N, upper_N]; exact N.lower_succ ar len y h

-- the lemmas of arrays.dfy

-- the row update of a two-dimensional array over any dependency, by induction on it
theorem current_trace_row_list (r : Int) (V : Int → Int) :
    ∀ (ds : List Int) (A0 : Int → Int → Int),
      current (trace A0 ds (fun A j => fun j1 => if j1 = r then fun j1 => if j1 = j then V j else A r j1 else A j1))
        = (fun j => if j = r then current (trace (A0 r) ds (fun b j => fun j1 => if j1 = j then V j else b j1))
                    else A0 j) := by
  intro ds
  induction ds with
  | nil => intro A0; funext j; by_cases h : j = r <;> simp [trace, current, h]
  | cons d ds ih =>
    intro A0
    simp only [trace, current]
    rw [ih]
    funext j
    by_cases h : j = r <;> simp [h]

theorem current_trace_row : Stmt.current_trace_row := by
  intro A0 r n V; exact current_trace_row_list r V _ A0

theorem trace_read_initial : Stmt.trace_read_initial := by
  intro α β _ _ a keys fs n hkeys hfs; exact N.trace_read_initial a keys fs keys.length rfl (by omega)

theorem stores_cases : Stmt.stores_cases := by
  intro a0 n c P G
  conv => rhs; simp (disch := complement) only [cases_of]
  rw [counter_N]; exact N.stores_cases a0 n.toNat c P G

theorem stores_read_unmodified : Stmt.stores_read_unmodified := by
  intro a0 n hs F hhs h
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n = m := ⟨hs.length, hhs.symm⟩
  simp only [counter_N, Int.toNat_natCast] at h ⊢
  exact N.stores_read_unmodified a0 m hs F (by omega) (by simp only [N.integer_cast]; exact h)

-- the shift of i + 1, ..., i + m one position down, by induction on the iterations: the first moves a[i + 1] to i,
-- the rest read the positions above i + 1, which it has not written
theorem select_current_trace_shift_N (m : Nat) : ∀ (a : Int → Int) (i j : Int),
    current (trace a (butlast (N.counter i 1 m)) (fun x k => fun l => if l = k then x (k + 1) else x l)) j
      = if i ≤ j ∧ j < i + m then a (j + 1) else a j := by
  induction m with
  | zero => intro a i j; simp only [N.counter, butlast, trace, current]; rw [if_neg (by omega)]
  | succ m ih =>
    intro a i j
    rw [N.butlast_counter_succ]
    simp only [trace]
    simp only [current]
    rw [ih]
    by_cases h1 : i + 1 ≤ j ∧ j < i + 1 + m
    · rw [if_pos h1, if_neg (by omega : ¬j + 1 = i), if_pos (by omega)]
    · rw [if_neg h1]
      by_cases e : j = i
      · subst e; rw [if_pos rfl, if_pos (by omega)]
      · rw [if_neg e, if_neg (by omega)]

theorem select_current_shifts : Stmt.select_current_shifts := by
  unfold Stmt.select_current_shifts; choices
  intro a i n j hn
  rw [shifts, counter_N, select_current_trace_shift_N, Int.toNat_of_nonneg hn]

-- the permutations of aggregation.dfy, after the shift of arrays.dfy: equal multiplicities are equal multisets, a swap
-- stores the values of two positions at each other, and the shift moves the values over the counter one position down
theorem mk_eq_of_count {α : Type} [Inhabited α] (xs ys : List α) (h : ∀ e, N.count e xs = N.count e ys) :
    Bag.mk xs = Bag.mk ys := by
  apply Quotient.sound
  apply List.perm_iff_count.2
  intro e
  have he := h e
  rw [← count_mk, ← count_mk] at he
  have : ((xs.count e : Nat) : Int) = ((ys.count e : Nat) : Int) := he
  omega

-- the multiplicities after a swap, over keys of any type, whose conditionals are those of the generic definitions
theorem count_selects_swap {α β : Type} [Inhabited α] [Inhabited β] (a b : α → β) (p q : α) (keys : List α)
    (hd : distincts keys) (hp : occurs p keys) (hq : occurs q keys)
    (hb : ∀ j, b j = if j = q then a p else if j = p then a q else a j) (e : β) :
    N.count e (selects b keys) = N.count e (selects a keys) := by
  rw [show b = fun j => if j = q then a p else (fun j => if j = p then a q else a j) j from funext hb,
    fold_selects_update 0 (fun u => if u = e then 1 else 0) (N.count e) rfl (fun _ _ => rfl) _ q (a p) keys hd,
    if_pos hq,
    fold_selects_update 0 (fun u => if u = e then 1 else 0) (N.count e) rfl (fun _ _ => rfl) a p (a q) keys hd, if_pos hp]
  by_cases e1 : q = p
  · subst e1; simp only [↓reduceIte]; omega
  · simp only [if_neg e1]; omega

theorem elems_selects_swap : Stmt.elems_selects_swap := by
  intro a p q v w keys n hkeys ⟨hd, hp, hq, hv, hw⟩
  rw [elems_mk, elems_mk]
  apply mk_eq_of_count
  apply count_selects_swap a _ p q keys hd hp hq
  intro j
  subst hv hw
  by_cases h1 : j = q <;> by_cases h2 : j = p <;> simp [h1, h2]

theorem butlast_counter_snoc (t : Nat) : ∀ (s : Int),
    butlast (N.counter s 1 (t + 1)) = butlast (N.counter s 1 t) ++ [s + t] := by
  induction t with
  | zero => intro s; simp [N.counter, butlast]
  | succ t ih =>
    intro s
    rw [N.butlast_counter_succ, ih (s + 1), N.butlast_counter_succ]
    simp only [List.cons_append, List.cons.injEq, true_and]; push_cast; rw [Int.add_assoc, Int.add_comm 1]

theorem selects_append {β : Type} [Inhabited β] (f : Int → β) (xs ys : List Int) :
    selects f (xs ++ ys) = selects f xs ++ selects f ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => show f x :: selects f (xs ++ ys) = f x :: (selects f xs ++ selects f ys); rw [ih]

theorem selects_succ_counter (a : Int → Int) (t : Nat) : ∀ (s : Int),
    selects (fun j => a (j + 1)) (butlast (N.counter s 1 t)) = selects a (butlast (N.counter (s + 1) 1 t)) := by
  induction t with
  | zero => intro s; rfl
  | succ t ih =>
    intro s
    rw [N.butlast_counter_succ, N.butlast_counter_succ]
    show a (s + 1) :: selects (fun j => a (j + 1)) _ = a (s + 1) :: selects a _
    rw [ih (s + 1)]

-- the values of the shift over i, ..., i + t: those of the original at i + 1, ..., i + t, and the last one again
theorem selects_shift (a : Int → Int) (i : Int) (t : Nat) :
    selects (current (shifts a (butlast (N.counter i 1 t))))
      (butlast (N.counter i 1 t)) = selects a (butlast (N.counter (i + 1) 1 t)) := by
  rw [← selects_succ_counter]
  apply N.maps_counter_congr_gen
  intro k hk
  rw [shifts, select_current_trace_shift_N, if_pos hk]

-- the difference of the first element, which erases it
theorem diff_single_head {α : Type} [Inhabited α] (x : α) (xs : List α) : Bag.diff (x :: xs) [x] = xs := by
  rw [Bag.diff, Bag.diff, List.erase_cons_head]

theorem elems_selects_shift : Stmt.elems_selects_shift := by
  intro a i n m ⟨hn, hm⟩
  obtain ⟨t, rfl⟩ : ∃ t : Nat, n = t := ⟨n.toNat, by omega⟩
  subst hm
  rw [counter_N, counter_N, Int.toNat_natCast, show ((t : Int) + 1).toNat = t + 1 by omega, elems_mk, elems_mk,
    butlast_counter_snoc, selects_append, selects_shift, ← butlast_counter_snoc, N.butlast_counter_succ]
  show Bag.mk (selects a (butlast (N.counter (i + 1) 1 t)) ++ [_])
    = Bag.mk (Bag.diff (a i :: selects a (butlast (N.counter (i + 1) 1 t))) [a i] ++ [a (i + t)])
  rw [diff_single_head]; dsimp only; rw [shifts, select_current_trace_shift_N, if_neg (by omega)]

theorem elems_selects_rotate : Stmt.elems_selects_rotate := by
  intro a i n m l v ⟨hn, hm, hl, hv⟩
  subst hl
  obtain ⟨t, rfl⟩ : ∃ t : Nat, n = t := ⟨n.toNat, by omega⟩
  subst hm hv
  rw [counter_N, counter_N, Int.toNat_natCast, show ((t : Int) + 1).toNat = t + 1 by omega, elems_mk, elems_mk,
    butlast_counter_snoc, selects_append]
  have hc : selects (fun j => if j = i + t then a i
      else current (shifts a (butlast (N.counter i 1 t))) j)
      (butlast (N.counter i 1 t))
      = selects (current (shifts a (butlast (N.counter i 1 t))))
      (butlast (N.counter i 1 t)) := by
    apply N.maps_counter_congr_gen
    intro k hk
    dsimp only; rw [if_neg (by omega)]
  rw [hc, selects_shift, ← butlast_counter_snoc, N.butlast_counter_succ]
  show Bag.mk (selects a (butlast (N.counter (i + 1) 1 t)) ++ [if i + t = i + t then a i else _])
    = Bag.mk (a i :: selects a (butlast (N.counter (i + 1) 1 t)))
  rw [if_pos rfl]
  exact Quotient.sound List.perm_append_comm

theorem selects_stores_counter : Stmt.selects_stores_counter := by
  intro a i c n vs hvs; rw [counter_N]; exact N.selects_stores_counter a i c n.toNat vs (by omega)

theorem select_current_trace_reset_keep : Stmt.select_current_trace_reset_keep := by
  intro a0 j n c
  conv => rhs; simp (disch := complement) only [cases_of]
  rw [counter_N, N.select_current_trace_reset_keep]
  exact ite_iff (toNat_zero_iff n) _ _

theorem length_stores_where : Stmt.length_stores_where := by
  intro a i c n guards values n1 hguards hvalues hn h
  rw [stores_where, N.length_butlast_trace, counter_N,
    N.length_zip_eq _ _ n.toNat (N.length_butlast_counter i c n.toNat)
      (by rw [N.length_zip_eq guards values guards.length rfl (by omega)]; omega)]
  omega

theorem earlier_stores_where : Stmt.earlier_stores_where := by
  intro j a i c n guards values n1 hguards hvalues hn ⟨hj, hjn⟩
  rw [stores_where, stores_where, earlier_trace_int j _ _ _ hj
    (by rw [counter_N, N.length_zip_eq _ _ n.toNat (N.length_butlast_counter i c n.toNat)
      (by rw [N.length_zip_eq guards values guards.length rfl (by omega)]; omega)]; omega),
    prefix_zip_int, prefix_zip_int, counter_N, counter_N, prefix_N,
    N.prefix_counter j.toNat i c n.toNat (by rw [N.integer_cast, N.integer_cast]; omega)]

theorem prefix_stores_where : Stmt.prefix_stores_where := by
  intro k a i c n guards values n1 hguards hvalues hn
  rw [stores_where, stores_where, prefix_trace_int, ← prefix_zip_int, counter_N, counter_N, prefix_N, prefix_N,
    prefix_zip_counter c k.toNat i n.toNat _
      (by rw [N.length_zip_eq guards values guards.length rfl (by omega)]; omega)]

-- the stores where the guards hold, over distinct keys: a key keeps the value of its iteration if its guard holds,
-- since it is written once
theorem select_current_stores_where_list (j : Int) : ∀ (a0 : Int → Int) (ks : List Int) (gs : List Prop) (vs : List Int),
    distincts ks → gs.length = ks.length → vs.length = ks.length →
    current (trace a0 (List.zip ks (List.zip gs vs))
      (fun b ⟨k, g, v⟩ => if g then fun j => if j = k then v else b j else if ¬g then b else unspecified)) j
      = if occurs j ks ∧ earlier (indexof j ks) gs then earlier (indexof j ks) vs else a0 j
  | a0, [], gs, vs, _, hg, hv => by
    rw [List.length_eq_zero_iff.1 hg, List.length_eq_zero_iff.1 hv]
    show a0 j = _
    rw [if_neg (fun h => h.1)]
  | a0, k :: ks, [], _, _, hg, _ => by simp at hg
  | a0, k :: ks, _, [], _, _, hv => by simp at hv
  | a0, k :: ks, g :: gs, v :: vs, hd, hg, hv => by
    simp only [distincts] at hd
    rw [List.zip_cons_cons, List.zip_cons_cons, N.trace_cons, N.current_step_eq,
      select_current_stores_where_list j _ ks gs vs hd.2 (by simpa using hg) (by simpa using hv)]
    dsimp only
    have hi : 0 ≤ indexof j ks := by rw [indexof_N]; omega
    have e : ∀ {γ : Type} [Inhabited γ] (x : γ) (xs : List γ),
        earlier (indexof j ks + 1) (x :: xs) = earlier (indexof j ks) xs := by
      intro γ _ x xs; simp only [earlier]; rw [if_neg (by omega), if_neg (by omega), Int.add_sub_cancel]
    by_cases ho : occurs j ks
    · have hk : k ≠ j := fun h => hd.1 (h ▸ ho)
      have hix : indexof j (k :: ks) = indexof j ks + 1 := by simp only [indexof]; rw [if_pos ho]
      rw [hix, e, e]
      by_cases hc : earlier (indexof j ks) gs
      · rw [if_pos (⟨ho, hc⟩ : occurs j ks ∧ earlier (indexof j ks) gs),
          if_pos (⟨Or.inr ho, hc⟩ : occurs j (k :: ks) ∧ earlier (indexof j ks) gs)]
      · rw [if_neg (fun h : occurs j ks ∧ earlier (indexof j ks) gs => hc h.2),
          if_neg (fun h : occurs j (k :: ks) ∧ earlier (indexof j ks) gs => hc h.2)]
        by_cases hg0 : g <;> simp [hg0, Ne.symm hk]
    · have hix : indexof j (k :: ks) = 0 := by simp only [indexof]; rw [if_neg ho]
      have e0 : ∀ {γ : Type} [Inhabited γ] (x : γ) (xs : List γ), earlier 0 (x :: xs) = x := by
        intro γ _ x xs; rfl
      rw [if_neg (fun h : occurs j ks ∧ earlier (indexof j ks) gs => ho h.1), hix, e0, e0]
      by_cases hk : k = j
      · subst hk
        by_cases hg0 : g
        · rw [if_pos (⟨Or.inl rfl, hg0⟩ : occurs k (k :: ks) ∧ g)]; simp [hg0]
        · rw [if_neg (fun h : occurs k (k :: ks) ∧ g => hg0 h.2)]; simp [hg0]
      · rw [if_neg (fun h : occurs j (k :: ks) ∧ g => h.1.elim hk ho)]
        by_cases hg0 : g <;> simp [hg0, Ne.symm hk]

theorem select_current_stores_where : Stmt.select_current_stores_where := by
  intro a0 i c n guards values j n1 hguards hvalues hn hc
  conv => rhs; simp (disch := complement) only [cases_of]
  have hl : (butlast (counter i c n)).length = n.toNat := by rw [counter_N, N.length_butlast_counter]
  rw [stores_where]
  exact select_current_stores_where_list j a0 _ guards values (distincts_counter i c n hc) (by omega) (by omega)

theorem length_copies : Stmt.length_copies := by
  intro a ks ls S n hks hls
  rw [copies, N.length_butlast_trace, N.length_zip_eq ks ls ks.length rfl (by omega)]

theorem earlier_copies : Stmt.earlier_copies := by
  intro j a ks ls S n hks hls ⟨hj, hjn⟩
  rw [copies, copies, earlier_trace_int j _ _ _ hj
    (by rw [N.length_zip_eq ks ls ks.length rfl (by omega)]; omega), prefix_zip_int]

theorem prefix_copies : Stmt.prefix_copies := by
  intro k a ks ls S n hks hls; rw [copies, copies, prefix_trace_int, prefix_zip_int]

-- the copies of S at both keys of each iteration: a position that is one of the keys has the value of S
theorem select_current_copies_list (S : Int → Int) (j : Int) : ∀ (ks ls : List Int) (a0 : Int → Int),
    ks.length = ls.length → current (copies a0 ks ls S) j = if occurs j ks ∨ occurs j ls then S j else a0 j
  | [], [], a0, _ => by show a0 j = _; simp [occurs]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | p :: ks, q :: ls, a0, h => by
    show current (copies (fun j => if j = q then S q else (fun j => if j = p then S p else a0 j) j) ks ls S) j = _
    rw [select_current_copies_list S j ks ls _ (by simpa using h)]
    simp only [occurs]
    by_cases hq : q = j
    · subst hq; simp
    · by_cases hp : p = j
      · subst hp; simp [Ne.symm hq]
      · simp [hp, hq, Ne.symm hp, Ne.symm hq]

theorem select_current_copies : Stmt.select_current_copies := by
  intro a0 ks ls S j n hks hls
  conv => rhs; simp (disch := complement) only [cases_of]
  exact select_current_copies_list S j ks ls a0 (by omega)

theorem select_current_trace_cap : Stmt.select_current_trace_cap := by
  intro a0 n j b
  conv => rhs; simp (disch := complement) only [cases_of]
  rw [counter_N, N.select_current_trace_cap, N.integer_cast]
  exact ite_iff ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩⟩ _ _

theorem store_select_other : Stmt.store_select_other := N.store_select_other

-- the lemmas of counters.dfy

theorem current_trace_constant : Stmt.current_trace_constant := by
  unfold Stmt.current_trace_constant; choices
  intro α _ x y i c n
  rw [counter_N, N.current_trace_constant]
  exact ite_iff (toNat_zero_iff n) _ _

theorem current_trace_last : Stmt.current_trace_last := by
  unfold Stmt.current_trace_last; choices
  intro α _ x0 n hs F hhs
  rw [counter_N]
  by_cases hn : n ≤ 0
  · rw [if_pos hn, show n.toNat = 0 by omega]; rfl
  · rw [if_neg hn, show n.toNat = (n - 1).toNat + 1 by omega, N.current_trace_last_from F (n - 1).toNat 0 x0 hs
      (by omega), earlier_N_nonneg _ _ (by omega)]
    congr 1; omega

-- phases: the model of Semantics.lean is the trace over the counter from 0 with the update by the phase of k
theorem iterations_N (t : Nat) : ∀ (s : Int), iterations s t = butlast (N.counter s 1 t) := by
  induction t with
  | zero => intro s; rfl
  | succ t ih => intro s; rw [N.butlast_counter_succ, ← ih]; rfl

theorem phases_trace (x0 m n : Int) (F G : Int → Int → Int) :
    phases x0 m n F G = trace x0 (butlast (counter 0 1 n)) (fun x k => if k < m then F x k else G x k) := by
  rw [phases, iterations_N, counter_N]

-- traces over a counter whose updates agree at its values are equal
theorem trace_counter_congr {α : Type} (f g : α → Int → α) (t : Nat) : ∀ (s : Int) (x : α),
    (∀ y k, s ≤ k → k < s + t → f y k = g y k) →
    trace x (butlast (N.counter s 1 t)) f = trace x (butlast (N.counter s 1 t)) g := by
  induction t with
  | zero => intro s x h; rfl
  | succ t ih =>
    intro s x h
    rw [N.butlast_counter_succ, N.trace_cons, N.trace_cons, h x s (Int.le_refl s) (by omega),
      ih (s + 1) _ (fun y k h1 h2 => h y k (by omega) (by omega))]

-- the counter of a + b steps is that of a steps followed by that of b steps from s + a
theorem butlast_counter_append (a : Nat) : ∀ (s : Int) (b : Nat),
    butlast (N.counter s 1 (a + b)) = butlast (N.counter s 1 a) ++ butlast (N.counter (s + a) 1 b) := by
  induction a with
  | zero => intro s b; simp [N.counter, butlast]
  | succ a ih =>
    intro s b
    rw [show a + 1 + b = (a + b) + 1 by omega, N.butlast_counter_succ, N.butlast_counter_succ, ih (s + 1) b,
      show s + 1 + (a : Int) = s + ((a + 1 : Nat) : Int) by omega]; rfl

theorem current_trace_append {α β : Type} [Inhabited α] (x : α) (l₁ l₂ : List β) (f : α → β → α) :
    current (trace x (l₁ ++ l₂) f) = current (trace (current (trace x l₁ f)) l₂ f) := by
  induction l₁ generalizing x with
  | nil => rfl
  | cons d ds ih => exact ih (f x d)

-- a counter from s + m read at k is one from s read at k + m
theorem trace_counter_shift {α : Type} (G : α → Int → α) (m : Int) (t : Nat) : ∀ (s : Int) (x : α),
    trace x (butlast (N.counter (s + m) 1 t)) G = trace x (butlast (N.counter s 1 t)) (fun y k => G y (k + m)) := by
  induction t with
  | zero => intro s x; rfl
  | succ t ih =>
    intro s x
    rw [N.butlast_counter_succ, N.butlast_counter_succ, N.trace_cons, N.trace_cons,
      show s + m + 1 = s + 1 + m by omega, ih (s + 1)]

theorem length_phases : Stmt.length_phases := by
  intro x0 m n F G h; rw [phases_trace, N.length_butlast_trace, counter_N, N.length_butlast_counter]; omega

theorem earlier_phases : Stmt.earlier_phases := by
  intro j x0 m n F G ⟨hj, hjn⟩
  rw [phases_trace, phases_trace, earlier_trace_int j _ _ _ hj
    (by rw [counter_N, N.length_butlast_counter]; omega), prefix_counter j 0 1 n (by omega)]

theorem prefix_phases : Stmt.prefix_phases := by
  intro k x0 m n F G h; rw [phases_trace, phases_trace, prefix_trace_int, prefix_counter k 0 1 n h]

-- below the threshold b the value counts up from x0 by 1, above it it stays at least b, hence the guard on the value
-- is the guard on the iteration
theorem trace_threshold_N (x0 b c : Int) (hc : 0 ≤ c) (t : Nat) : ∀ (s x : Int), 0 ≤ s →
    (s ≤ b - x0 → x = x0 + s) → (b - x0 ≤ s → b ≤ x) →
    trace x (butlast (N.counter s 1 t)) (fun x k => if x < b then x + 1 else x + c)
      = trace x (butlast (N.counter s 1 t)) (fun x k => if k < b - x0 then x + 1 else x + c) := by
  induction t with
  | zero => intro s x hs h1 h2; rfl
  | succ t ih =>
    intro s x hs h1 h2
    rw [N.butlast_counter_succ, N.trace_cons, N.trace_cons]
    by_cases hk : s < b - x0
    · rw [if_pos (show x < b by have := h1 (by omega); omega), if_pos hk]
      rw [ih (s + 1) (x + 1) (by omega) (fun h => by have := h1 (by omega); omega)
        (fun h => by have := h1 (by omega); omega)]
    · rw [if_neg (show ¬x < b by have := h2 (by omega); omega), if_neg hk]
      rw [ih (s + 1) (x + c) (by omega) (fun h => by omega) (fun h => by have := h2 (by omega); omega)]

theorem trace_threshold : Stmt.trace_threshold := by
  intro x0 n b c ⟨hb, hc⟩
  choices
  rw [phases_trace, counter_N]
  exact trace_threshold_N x0 b c hc n.toNat 0 x0 (Int.le_refl 0) (fun _ => by omega) (fun h => by omega)

theorem current_phases : Stmt.current_phases := by
  intro x0 m n F G ⟨hm, hn⟩
  choices
  rw [phases_trace]
  by_cases h : n ≤ m
  · rw [if_pos h, counter_N]
    congr 1
    exact trace_counter_congr _ _ n.toNat 0 x0 (fun y k h1 h2 => by rw [if_pos (by omega)])
  · rw [if_neg h, counter_N, counter_N, counter_N,
      show n.toNat = m.toNat + (n - m).toNat by omega, butlast_counter_append, current_trace_append,
      trace_counter_congr _ (fun x k => F x k) m.toNat 0 x0 (fun y k h1 h2 => by rw [if_pos (by omega)]),
      trace_counter_congr _ (fun x k => G x k) (n - m).toNat _ _ (fun y k h1 h2 => by rw [if_neg (by omega)]),
      show (0 : Int) + (m.toNat : Int) = 0 + m by omega, trace_counter_shift]

-- the states of a trace that does not decrease are below a bound iff the last of them is
theorem invs_butlast_mono (h : Int → Int → Int) (hm : ∀ y k, y ≤ h y k) (B : Int) (t : Nat) : ∀ (s x : Int),
    invs (butlast (trace x (butlast (N.counter s 1 (t + 1))) h)) (fun x => x < B)
      ↔ current (trace x (butlast (N.counter s 1 t)) h) < B := by
  induction t with
  | zero => intro s x; simp [N.counter, butlast, trace, invs, current]
  | succ t ih =>
    intro s x
    rw [N.butlast_counter_succ, N.trace_cons, butlast, invs, ih (s + 1) (h x s), N.butlast_counter_succ,
      N.trace_cons, N.current_step_eq]
    have := N.trace_mono (h x s) (butlast (N.counter (s + 1) 1 t)) h hm
    have := hm x s
    constructor
    · exact fun h => h.2
    · exact fun h' => ⟨by omega, h'⟩

-- a predicate of the second components of a zip with a list at least as long
theorem invs_zip_snd {α β : Type} (P : β → Prop) : ∀ (ks : List α) (xs : List β), xs.length ≤ ks.length →
    (invs (List.zip ks xs) (fun p => P p.2) ↔ invs xs P)
  | _, [], _ => by simp [invs]
  | [], _ :: _, h => by simp at h
  | k :: ks, x :: xs, h => by
    rw [List.zip_cons_cons, invs, invs, invs_zip_snd P ks xs (by simp at h; omega)]

theorem invs_phases_upper : Stmt.invs_phases_upper := by
  intro x0 m n F G B ⟨hm, hFG⟩
  have hmono : ∀ y k, y ≤ (fun x k => if k < m then F x k else G x k) y k := by
    intro y k; dsimp only; split
    · exact (hFG y k).1
    · exact (hFG y k).2
  rw [phases_trace, phases_trace]
  show invs (List.zip _ _) (fun p => p.2 < B) ↔ _
  rw [invs_zip_snd (fun x => x < B) _ _ (by rw [N.length_butlast_trace]; exact Nat.le_refl _)]
  by_cases hn : n ≤ 0
  · rw [counter_N, show n.toNat = 0 by omega]; simp [N.counter, butlast, trace, invs, hn]
  · rw [counter_N, counter_N, show n.toNat = (n - 1).toNat + 1 by omega, invs_butlast_mono _ hmono B]
    simp only [hn, false_or]

theorem current_trace_catch_up : Stmt.current_trace_catch_up := by
  intro y0 x0 n ⟨hn, h⟩
  conv => rhs; simp (disch := complement) only [cases_of]
  rw [counter_N, counter_N, N.current_trace_catch_up y0 x0 n.toNat h, N.integer_cast, Int.toNat_of_nonneg hn]

theorem current_trace_flag : Stmt.current_trace_flag := by
  intro α _ x0 c n hs D hhs
  conv => rhs; simp (disch := complement) only [cases_of]
  rw [counter_N]; exact N.current_trace_flag x0 c n.toNat hs D (by omega)

theorem current_trace_bounded : Stmt.current_trace_bounded := by
  intro x0 n lo hi C1 C2 C3 F1 F2 F3 h
  rw [counter_N]; exact N.current_trace_bounded x0 n.toNat lo hi C1 C2 C3 F1 F2 F3 h

-- the lemmas of strides.dfy

theorem occurs_counter_step : Stmt.occurs_counter_step := by
  intro i d n j ⟨hn, hd⟩
  rw [counter_N, N.occurs_counter_step i d n.toNat j hd, N.integer_cast, Int.toNat_of_nonneg hn]

theorem indexof_counter_step : Stmt.indexof_counter_step := by
  intro j i d n ⟨hd, h1, h2, h3⟩
  rcases Int.lt_or_le n 0 with hn | hn
  · have : n * d < 0 := Int.mul_neg_of_neg_of_pos hn hd
    omega
  · rw [indexof_N, counter_N, N.indexof_counter_step j i d n.toNat
      ⟨hd, h1, by rw [N.integer_cast, Int.toNat_of_nonneg hn]; exact h2, h3⟩, N.natural_eq,
      Int.toNat_of_nonneg (Int.ediv_nonneg (by omega) (by omega))]

-- the stores of w adjacent cells from the positions of a counter by s ≥ w, with the values V d r at the offset r of
-- the iteration of the dependency d: the read at j is that of the iteration (j - t) / s at the offset (j - t) % s if
-- the offset is within the window, by induction over the remaining iterations from the position t
theorem window_from {β : Type} [Inhabited β] (s w : Int) (hw : 0 < w) (hws : w ≤ s) (V : β → Int → Int)
    (U : (Int → Int) → Int × β → Int → Int)
    (hU : ∀ a p d i, U a (p, d) i = if p ≤ i ∧ i < p + w then V d (i - p) else a i) (j : Int) (r : Nat) :
    ∀ (b : Int → Int) (t : Int) (ds : List β), ds.length = r →
    current (trace b (List.zip (butlast (N.counter t s r)) ds) U) j
      = if t ≤ j ∧ j < t + s * r ∧ (j - t) % s < w then V (N.earlier ((j - t) / s).toNat ds) ((j - t) % s)
        else b j := by
  induction r with
  | zero =>
    intro b t ds hds
    simp only [N.counter, butlast, List.zip_nil_left, N.current_trace_nil]; rw [if_neg (by omega)]
  | succ r ih =>
    intro b t ds hds
    cases ds with
    | nil => simp at hds
    | cons d ds =>
      rw [N.butlast_counter_succ, List.zip_cons_cons, N.trace_cons, N.current_step_eq,
        ih _ _ ds (by simp at hds; omega), hU]
      have hr : s * ((r + 1 : Nat) : Int) = s * r + s := by rw [Int.natCast_add, Int.mul_add]; simp
      have hsr : 0 ≤ s * (r : Int) := Int.mul_nonneg (by omega) (by omega)
      have hm : (j - (t + s)) % s = (j - t) % s := by
        rw [show j - (t + s) = j - t - s by omega, Int.sub_emod_right]
      rw [hr, hm]
      by_cases h1 : t + s ≤ j ∧ j < t + s + s * r ∧ (j - t) % s < w
      · have hq : (j - t) / s = (j - (t + s)) / s + 1 := by
          rw [show j - t = (j - (t + s)) + s * 1 by omega, Int.add_mul_ediv_left _ _ (by omega)]
        have hn : 0 ≤ (j - (t + s)) / s := Int.ediv_nonneg (by omega) (by omega)
        rw [if_pos h1, if_pos ⟨by omega, by omega, h1.2.2⟩, hq, show ((j - (t + s)) / s + 1).toNat
          = ((j - (t + s)) / s).toNat + 1 by omega]
        rfl
      · rw [if_neg h1]
        by_cases h2 : t ≤ j ∧ j < t + w
        · have he : (j - t) % s = j - t := Int.emod_eq_of_lt (by omega) (by omega)
          have hd : (j - t) / s = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
          rw [if_pos h2, if_pos ⟨h2.1, by omega, by omega⟩, he, hd]; rfl
        · rw [if_neg h2, if_neg]
          intro ⟨h3, h4, h5⟩
          by_cases h6 : j - t < s
          · rw [Int.emod_eq_of_lt (by omega) h6] at h5; omega
          · exact h1 ⟨by omega, by omega, h5⟩

-- the read of the final array of the stores at the positions of a counter from o by s, over integers
theorem window_read {β : Type} [Inhabited β] (s w : Int) (hw : 0 < w) (hws : w ≤ s) (V : β → Int → Int)
    (U : (Int → Int) → Int × β → Int → Int)
    (hU : ∀ a p d i, U a (p, d) i = if p ≤ i ∧ i < p + w then V d (i - p) else a i)
    (a0 : Int → Int) (o n j : Int) (ds : List β) (hds : ds.length = n) :
    current (trace a0 (List.zip (butlast (counter o s n)) ds) U) j
      = if 0 ≤ j - o ∧ j - o < s * n ∧ (j - o) % s < w then V (earlier ((j - o) / s) ds) ((j - o) % s)
        else a0 j := by
  rw [counter_N, window_from s w hw hws V U hU j n.toNat a0 o ds (by omega), Int.toNat_of_nonneg (by omega)]
  by_cases h : 0 ≤ j - o ∧ j - o < s * n ∧ (j - o) % s < w
  · rw [if_pos ⟨by omega, by omega, h.2.2⟩, if_pos h, earlier_N_nonneg _ _ (Int.ediv_nonneg h.1 (by omega))]
  · rw [if_neg (fun h' => h ⟨by omega, by omega, h'.2.2⟩), if_neg h]

-- the reads of a zip are the pairs of the reads, within the lists
theorem earlier_zip {α β : Type} [Inhabited α] [Inhabited β] (xs : List α) (ys : List β) :
    ∀ (k : Int), 0 ≤ k → k < xs.length → xs.length = ys.length →
      earlier k (List.zip xs ys) = (earlier k xs, earlier k ys) := by
  induction xs generalizing ys with
  | nil => intro k _ h; simp at h; omega
  | cons x xs ih =>
    intro k hk hkl hl
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.zip_cons_cons, earlier, if_neg (show ¬k < 0 by omega)]
      by_cases e : k = 0
      · simp only [e, ↓reduceIte]
      · simp only [e, ↓reduceIte]
        exact ih ys (k - 1) (by omega) (by simp at hkl; omega) (by simp at hl; omega)

-- the index of a read within the window is within the lists
theorem window_index (s n j o : Int) (hs : 0 < s) (h : 0 ≤ j - o ∧ j - o < s * n) :
    0 ≤ (j - o) / s ∧ (j - o) / s < n :=
  ⟨Int.ediv_nonneg h.1 (by omega), Int.ediv_lt_of_lt_mul hs (by rw [Int.mul_comm]; exact h.2)⟩

theorem select_current_strides₂ : Stmt.select_current_strides₂ := by
  intro a0 o s n xs₀ xs₁ j h₀ h₁ hs
  rw [strides₂, window_read s 2 (by decide) hs (fun (x : Int × Int) r => if r = 0 then x.1 else x.2) _
    (fun a p x i => by
      obtain ⟨x₀, x₁⟩ := x; dsimp only
      by_cases e₁ : i = p + 1
      · rw [if_pos e₁, if_pos (by omega), if_neg (by omega)]
      · rw [if_neg e₁]; by_cases e₀ : i = p
        · rw [if_pos e₀, if_pos (by omega), if_pos (by omega)]
        · rw [if_neg e₀, if_neg (by omega)]) a0 o n j _
    (by rw [N.length_zip_eq xs₀ xs₁ xs₀.length rfl (by omega)]; omega)]
  have hm := Int.emod_nonneg (j - o) (show s ≠ 0 by omega)
  by_cases h : 0 ≤ j - o ∧ j - o < s * n ∧ (j - o) % s < 2
  · have hi := window_index s n j o (by omega) ⟨h.1, h.2.1⟩
    rw [if_pos h, earlier_zip xs₀ xs₁ _ hi.1 (by omega) (by omega)]
    dsimp only; repeat' split
    all_goals first | rfl | omega
  · rw [if_neg h]; repeat' split
    all_goals first | rfl | omega

theorem select_current_strides₃ : Stmt.select_current_strides₃ := by
  intro a0 o s n xs₀ xs₁ xs₂ j h₀ h₁ h₂ hs
  have l₁ := N.length_zip_eq xs₁ xs₂ xs₁.length rfl (by omega)
  have l₀ := N.length_zip_eq xs₀ (List.zip xs₁ xs₂) xs₀.length rfl (by omega)
  rw [strides₃, window_read s 3 (by decide) hs
    (fun (x : Int × Int × Int) r => if r = 0 then x.1 else if r = 1 then x.2.1 else x.2.2) _
    (fun a p x i => by
      obtain ⟨x₀, x₁, x₂⟩ := x; dsimp only
      by_cases e₂ : i = p + 2
      · rw [if_pos e₂, if_pos (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg e₂]; by_cases e₁ : i = p + 1
        · rw [if_pos e₁, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        · rw [if_neg e₁]; by_cases e₀ : i = p
          · rw [if_pos e₀, if_pos (by omega), if_pos (by omega)]
          · rw [if_neg e₀, if_neg (by omega)]) a0 o n j _ (by omega)]
  have hm := Int.emod_nonneg (j - o) (show s ≠ 0 by omega)
  by_cases h : 0 ≤ j - o ∧ j - o < s * n ∧ (j - o) % s < 3
  · have hi := window_index s n j o (by omega) ⟨h.1, h.2.1⟩
    rw [if_pos h, earlier_zip xs₀ _ _ hi.1 (by omega) (by omega),
      earlier_zip xs₁ xs₂ _ hi.1 (by omega) (by omega)]
    dsimp only; repeat' split
    all_goals first | rfl | omega
  · rw [if_neg h]; repeat' split
    all_goals first | rfl | omega

theorem select_current_strides₄ : Stmt.select_current_strides₄ := by
  intro a0 o s n xs₀ xs₁ xs₂ xs₃ j h₀ h₁ h₂ h₃ hs
  have l₂ := N.length_zip_eq xs₂ xs₃ xs₂.length rfl (by omega)
  have l₁ := N.length_zip_eq xs₁ (List.zip xs₂ xs₃) xs₁.length rfl (by omega)
  have l₀ := N.length_zip_eq xs₀ (List.zip xs₁ (List.zip xs₂ xs₃)) xs₀.length rfl (by omega)
  rw [strides₄, window_read s 4 (by decide) hs
    (fun (x : Int × Int × Int × Int) r =>
      if r = 0 then x.1 else if r = 1 then x.2.1 else if r = 2 then x.2.2.1 else x.2.2.2) _
    (fun a p x i => by
      obtain ⟨x₀, x₁, x₂, x₃⟩ := x; dsimp only
      by_cases e₃ : i = p + 3
      · rw [if_pos e₃, if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg e₃]; by_cases e₂ : i = p + 2
        · rw [if_pos e₂, if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        · rw [if_neg e₂]; by_cases e₁ : i = p + 1
          · rw [if_pos e₁, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
          · rw [if_neg e₁]; by_cases e₀ : i = p
            · rw [if_pos e₀, if_pos (by omega), if_pos (by omega)]
            · rw [if_neg e₀, if_neg (by omega)]) a0 o n j _ (by omega)]
  have hm := Int.emod_nonneg (j - o) (show s ≠ 0 by omega)
  by_cases h : 0 ≤ j - o ∧ j - o < s * n ∧ (j - o) % s < 4
  · have hi := window_index s n j o (by omega) ⟨h.1, h.2.1⟩
    rw [if_pos h, earlier_zip xs₀ _ _ hi.1 (by omega) (by omega),
      earlier_zip xs₁ _ _ hi.1 (by omega) (by omega), earlier_zip xs₂ xs₃ _ hi.1 (by omega) (by omega)]
    dsimp only; repeat' split
    all_goals first | rfl | omega
  · rw [if_neg h]; repeat' split
    all_goals first | rfl | omega

theorem select_current_strides₅ : Stmt.select_current_strides₅ := by
  intro a0 o s n xs₀ xs₁ xs₂ xs₃ xs₄ j h₀ h₁ h₂ h₃ h₄ hs
  have l₃ := N.length_zip_eq xs₃ xs₄ xs₃.length rfl (by omega)
  have l₂ := N.length_zip_eq xs₂ (List.zip xs₃ xs₄) xs₂.length rfl (by omega)
  have l₁ := N.length_zip_eq xs₁ (List.zip xs₂ (List.zip xs₃ xs₄)) xs₁.length rfl (by omega)
  have l₀ := N.length_zip_eq xs₀ (List.zip xs₁ (List.zip xs₂ (List.zip xs₃ xs₄))) xs₀.length rfl (by omega)
  rw [strides₅, window_read s 5 (by decide) hs
    (fun (x : Int × Int × Int × Int × Int) r =>
      if r = 0 then x.1 else if r = 1 then x.2.1 else if r = 2 then x.2.2.1 else if r = 3 then x.2.2.2.1
      else x.2.2.2.2) _
    (fun a p x i => by
      obtain ⟨x₀, x₁, x₂, x₃, x₄⟩ := x; dsimp only
      by_cases e₄ : i = p + 4
      · rw [if_pos e₄, if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [if_neg e₄]; by_cases e₃ : i = p + 3
        · rw [if_pos e₃, if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        · rw [if_neg e₃]; by_cases e₂ : i = p + 2
          · rw [if_pos e₂, if_pos (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
          · rw [if_neg e₂]; by_cases e₁ : i = p + 1
            · rw [if_pos e₁, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
            · rw [if_neg e₁]; by_cases e₀ : i = p
              · rw [if_pos e₀, if_pos (by omega), if_pos (by omega)]
              · rw [if_neg e₀, if_neg (by omega)]) a0 o n j _ (by omega)]
  have hm := Int.emod_nonneg (j - o) (show s ≠ 0 by omega)
  by_cases h : 0 ≤ j - o ∧ j - o < s * n ∧ (j - o) % s < 5
  · have hi := window_index s n j o (by omega) ⟨h.1, h.2.1⟩
    rw [if_pos h, earlier_zip xs₀ _ _ hi.1 (by omega) (by omega),
      earlier_zip xs₁ _ _ hi.1 (by omega) (by omega), earlier_zip xs₂ _ _ hi.1 (by omega) (by omega),
      earlier_zip xs₃ xs₄ _ hi.1 (by omega) (by omega)]
    dsimp only; repeat' split
    all_goals first | rfl | omega
  · rw [if_neg h]; repeat' split
    all_goals first | rfl | omega

theorem select_current_trace_ahead : Stmt.select_current_trace_ahead := by
  unfold Stmt.select_current_trace_ahead; choices
  intro a0 n m F G j h
  rw [counter_N]
  rcases Int.lt_or_le n 0 with hn | hn
  · rw [show n.toNat = 0 by omega, if_neg (by omega), if_neg (by omega)]; rfl
  · rw [N.select_current_trace_ahead a0 n.toNat m F G j (by rw [N.integer_cast]; omega), N.integer_cast,
      Int.toNat_of_nonneg hn]

theorem select_current_trace_ahead_down : Stmt.select_current_trace_ahead_down := by
  intro a0 n s d P F G j hd
  rw [counter_N, counter_N]
  rcases Int.lt_or_le n 0 with hn | hn
  · rw [N.ahead_down_from P F G d j n.toNat a0 0 s (0 + (n.toNat : Int) - 1) (by omega) rfl,
      show n.toNat = 0 by omega]
    simp only [Nat.lt_irrefl, false_and, and_false, ↓reduceIte, not_false_eq_true, show ¬0 < n by omega]
    (repeat' (split <;> try dsimp only)) <;> first | rfl | omega |
      (simp only [and_true, Classical.not_and_iff_not_or_not] at *; omega)
  · rw [N.ahead_down_from P F G d j n.toNat a0 0 s (n - 1) (by omega) (by omega), Int.toNat_of_nonneg hn]
    by_cases hP : P (n - 1) <;> simp only [hP, and_true, and_false, not_false_eq_true, ↓reduceIte] <;>
      (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega |
        (simp only [not_false_eq_true, and_true, Classical.not_and_iff_not_or_not, Classical.not_not] at *; omega)

-- the tiles: the stores of the values vs at the positions s + o, s + 1 + o, ... of t iterations, at least as many
-- values as iterations, leave at j the value of vs at j - s - o within these positions, by induction on the iterations
theorem stores_counter_read (o j : Int) (t : Nat) : ∀ (b : Int → Int) (s : Int) (vs : List Int), t ≤ vs.length →
    current (stores b (maps (butlast (N.counter s 1 t)) (fun l => l + o)) vs) j
      = if s + o ≤ j ∧ j < s + t + o then earlier (j - s - o) vs else b j := by
  induction t with
  | zero => intro b s vs _; rw [if_neg (by omega)]; rfl
  | succ t ih =>
    intro b s vs hvs
    cases vs with
    | nil => simp at hvs
    | cons v vs =>
      rw [stores, N.butlast_counter_succ, maps, List.zip_cons_cons, N.trace_cons, N.current_step_eq, ← stores,
        ih _ _ vs (by simp at hvs; omega)]
      dsimp only
      by_cases h1 : j = s + o
      · subst h1
        rw [if_neg (by omega), if_pos rfl, if_pos (by omega), show s + o - s - o = 0 by omega]
        simp [earlier]
      · by_cases h2 : s + 1 + o ≤ j ∧ j < s + 1 + t + o
        · rw [if_pos h2, if_pos (by omega)]
          simp only [earlier, show ¬j - s - o < 0 by omega, show ¬j - s - o = 0 by omega, if_false,
            show j - s - o - 1 = j - (s + 1) - o by omega]
        · rw [if_neg h2, if_neg h1, if_neg (by omega)]

-- the tile of j, which the iteration j / m of the outer loop writes at its position j % m
theorem tile_iff (m s j : Int) (hm : 0 < m) : (0 + m * s ≤ j ∧ j < 0 + m.toNat + m * s) ↔ j / m = s := by
  have h1 := Int.le_ediv_iff_mul_le (a := s) (b := j) hm
  have h2 := Int.ediv_lt_iff_lt_mul (a := j) (b := s + 1) hm
  rw [Int.add_mul, Int.one_mul, Int.mul_comm s m] at *
  omega

-- the outer loop over the iterations s, ..., s + t - 1, each storing its tile, by induction on the iterations
theorem tiles_from (m : Int) (hm : 0 < m) (V : Int → List Int) (j : Int)
    (U : (Int → Int) → Int × Int → Int → Int)
    (hU : ∀ a k h, U a (k, h) = current (stores a (maps (butlast (N.counter 0 1 m.toNat)) (fun l => l + m * k)) (V k)))
    (t : Nat) : ∀ (b : Int → Int) (s : Int) (hs : List Int), hs.length = t →
    (∀ k, s ≤ k ∧ k < s + t → m ≤ (V k).length) →
    current (trace b (List.zip (butlast (N.counter s 1 t)) hs) U) j
      = if s ≤ j / m ∧ j / m < s + t then earlier (j % m) (V (j / m)) else b j := by
  induction t with
  | zero => intro b s hs _ _; rw [if_neg (by omega)]; rfl
  | succ t ih =>
    intro b s hs hhs hV
    cases hs with
    | nil => simp at hhs
    | cons h hs =>
      rw [N.butlast_counter_succ, List.zip_cons_cons, N.trace_cons, N.current_step_eq,
        ih _ _ hs (by simp at hhs; omega) (fun k hk => hV k (by omega))]
      by_cases e : j / m = s
      · rw [if_neg (by omega), if_pos (by omega), hU, stores_counter_read _ _ _ _ _ _ (by have := hV s (by omega); omega),
          if_pos ((tile_iff m s j hm).2 e), e, Int.emod_def, e]
        congr 1; omega
      · by_cases h2 : s + 1 ≤ j / m ∧ j / m < s + 1 + t
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega), hU, stores_counter_read _ _ _ _ _ _ (by have := hV s (by omega); omega),
            if_neg (fun h' => e ((tile_iff m s j hm).1 h'))]

theorem select_current_tiles : Stmt.select_current_tiles := by
  unfold Stmt.select_current_tiles; choices
  intro a0 n m hs V j hhs hV hm
  simp only [counter_N]
  rw [tiles_from m hm V j _ (fun a k h => rfl) n.toNat a0 0 hs (by omega) (fun k hk => hV k (by omega))]
  have h1 := Int.le_ediv_iff_mul_le (a := 0) (b := j) hm
  have h2 := Int.ediv_lt_iff_lt_mul (a := j) (b := n) hm
  rw [Int.zero_mul] at h1
  rw [Int.mul_comm n m] at h2
  exact ite_iff (by omega) _ _

-- the lemmas of unsigned.dfy

theorem length_mods : Stmt.length_mods := by
  intro i c m n hn; rw [mods, N.length_butlast_trace, counter_N, N.length_butlast_counter]; omega

theorem invs_mods_upper : Stmt.invs_mods_upper := by
  intro b i c m n h
  rw [mods_N, N.invs_mods_upper b i c m n.toNat h, N.integer_cast]
  rcases Int.lt_or_le n 0 with hn | hn
  · have h1 : ((n.toNat : Int) - 1) * c < 0 := Int.mul_neg_of_neg_of_pos (by omega) (by omega)
    have h2 : (n - 1) * c < 0 := Int.mul_neg_of_neg_of_pos (by omega) (by omega)
    constructor <;> intro _ <;> omega
  · rw [Int.toNat_of_nonneg hn]

theorem invs_mods_upper_cases : Stmt.invs_mods_upper_cases := by
  intro b i c m n h
  rw [mods_N, N.invs_mods_upper_cases b i c m n.toNat h, N.integer_cast, toNat_zero_iff]
  rcases Int.lt_or_le n 0 with hn | hn
  · exact ⟨fun _ => Or.inl (by omega), fun _ => Or.inl (by omega)⟩
  · rw [Int.toNat_of_nonneg hn]

theorem invs_mods_down : Stmt.invs_mods_down := by
  intro i c m n h
  rw [mods_N, N.invs_mods_down i c m n.toNat h, N.integer_cast]
  rcases Int.lt_or_le n 0 with hn | hn
  · have h1 : ((n.toNat : Int) - 1) * (m - c) < 0 := Int.mul_neg_of_neg_of_pos (by omega) (by omega)
    have h2 : (n - 1) * (m - c) < 0 := Int.mul_neg_of_neg_of_pos (by omega) (by omega)
    constructor <;> intro _ <;> omega
  · rw [Int.toNat_of_nonneg hn]

theorem invs_mods_down_cases : Stmt.invs_mods_down_cases := by
  intro i c m n h
  rw [mods_N, N.invs_mods_down_cases i c m n.toNat h, N.integer_cast, toNat_zero_iff]
  rcases Int.lt_or_le n 0 with hn | hn
  · exact ⟨fun _ => Or.inl (by omega), fun _ => Or.inl (by omega)⟩
  · rw [Int.toNat_of_nonneg hn]

theorem current_mods_up : Stmt.current_mods_up := by
  intro i c m n ⟨hn, h⟩
  rw [mods_N, N.current_mods_up i c m n.toNat (by rw [N.integer_cast, Int.toNat_of_nonneg hn]; exact h),
    N.integer_cast, Int.toNat_of_nonneg hn]

theorem current_mods : Stmt.current_mods := by
  intro i c m n ⟨hn, h⟩
  rw [mods_N, N.current_mods i c m n.toNat h, N.integer_cast, Int.toNat_of_nonneg hn]

theorem butlast_mods_up : Stmt.butlast_mods_up := by
  intro i c m n h
  rw [mods_N, counter_N]
  rcases Int.lt_or_le n 0 with hn | hn
  · rw [show n.toNat = 0 by omega]; rfl
  · exact N.butlast_mods_up i c m n.toNat (by rw [N.integer_cast, Int.toNat_of_nonneg hn]; exact h)

theorem invs_counter_mod_upper_zero : Stmt.invs_counter_mod_upper_zero := by
  intro b m n h
  rw [counter_N, N.invs_counter_mod_upper_zero b m n.toNat h, N.integer_cast]
  constructor <;> intro _ <;> omega

theorem invs_counter_mod_upper_cases : Stmt.invs_counter_mod_upper_cases := by
  intro b i m n h
  rw [counter_N, N.invs_counter_mod_upper_cases b i m n.toNat h, N.integer_cast, toNat_zero_iff]
  constructor <;> intro h0 <;> omega

theorem current_trace_mod_add_const : Stmt.current_trace_mod_add_const := by
  intro x0 n m c h; rw [counter_N]; exact N.current_trace_mod_add_const x0 n.toNat m c h

theorem current_trace_mod_add_cases : Stmt.current_trace_mod_add_cases := by
  intro x0 n m C F h; rw [counter_N]; exact N.current_trace_mod_add_cases x0 n.toNat m C F h

theorem current_trace_mod_affine : Stmt.current_trace_mod_affine := by
  intro x0 m n hs A B hhs ⟨h1, h2, h3⟩
  have := N.trace_mod_affine_from m A B (List.zip (butlast (counter 0 1 n)) hs) x0
  rwa [Int.emod_eq_of_lt h2 h3] at this

theorem current_trace_mod_affine_wrapped : Stmt.current_trace_mod_affine_wrapped := by
  intro y m n hs A B hhs _
  exact N.trace_mod_affine_from m A B (List.zip (butlast (counter 0 1 n)) hs) y

theorem current_trace_mod_mul : Stmt.current_trace_mod_mul := by
  intro x0 m n hs A hhs ⟨h1, h2, h3⟩
  have := N.trace_mod_mul_from m A (List.zip (butlast (counter 0 1 n)) hs) x0
  rwa [Int.emod_eq_of_lt h2 h3] at this

-- the lemmas of series.dfy

theorem squares_zero : Stmt.squares_zero := by
  intro i n hn; rw [squares_N, show n.toNat = 0 by omega]; exact N.squares_zero i

theorem cubes_zero : Stmt.cubes_zero := by
  intro i n hn; rw [cubes_N, show n.toNat = 0 by omega]; exact N.cubes_zero i

theorem fourths_zero : Stmt.fourths_zero := by
  intro i n hn; rw [fourths_N, show n.toNat = 0 by omega]; exact N.fourths_zero i

theorem fifths_zero : Stmt.fifths_zero := by
  intro i n hn; rw [fifths_N, show n.toNat = 0 by omega]; exact N.fifths_zero i

theorem squares_closed : Stmt.squares_closed := by
  intro i n hn; rw [squares_N, N.squares_closed, N.integer_cast, Int.toNat_of_nonneg hn]

theorem cubes_closed : Stmt.cubes_closed := by
  intro i n hn; rw [cubes_N, N.cubes_closed, N.integer_cast, Int.toNat_of_nonneg hn]

theorem fourths_closed : Stmt.fourths_closed := by
  intro i n hn; rw [fourths_N, N.fourths_closed, N.integer_cast, Int.toNat_of_nonneg hn]

theorem fifths_closed : Stmt.fifths_closed := by
  intro i n hn; rw [fifths_N, N.fifths_closed, N.integer_cast, Int.toNat_of_nonneg hn]

theorem current_trace_geometric : Stmt.current_trace_geometric := by
  intro y0 z n; rw [counter_N, pow_N]; exact N.current_trace_geometric y0 z n.toNat

theorem length_series : Stmt.length_series := by
  intro x0 z a n hn; rw [series, N.length_butlast_trace, counter_N, N.length_butlast_counter]; omega

theorem current_series_zero : Stmt.current_series_zero := by
  intro x0 z a n hn; rw [series_N, show n.toNat = 0 by omega]; rfl

theorem current_series_one : Stmt.current_series_one := by
  intro x0 z a; rw [series_N]; rfl

theorem current_series : Stmt.current_series := by
  intro x0 z a n; rw [series_N, pow_N]; exact N.current_series x0 z a n.toNat

end TEQ
