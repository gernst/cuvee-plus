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

theorem squares_N (i n : Int) : squares i n = N.squares i n.toNat := by
  simp only [squares, N.squares, counter_N]

theorem cubes_N (i n : Int) : cubes i n = N.cubes i n.toNat := by
  simp only [cubes, N.cubes, counter_N]

theorem fourths_N (i n : Int) : fourths i n = N.fourths i n.toNat := by
  simp only [fourths, N.fourths, counter_N]

theorem fifths_N (i n : Int) : fifths i n = N.fifths i n.toNat := by
  simp only [fifths, N.fifths, counter_N]

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
  intro α β _ _ k a keys values n hkeys hvalues
  rw [indexof_N, earlier_N_nonneg _ _ (by omega), Int.toNat_natCast]
  exact N.current_stores k a keys values n.toNat (by omega) (by omega)

theorem earlier_stores : Stmt.earlier_stores := by
  intro α β _ _ k j a keys values n hkeys hvalues ⟨hj, hjn⟩
  rw [earlier_N_nonneg j _ hj, prefix_N, indexof_N, earlier_N_nonneg _ _ (by omega), Int.toNat_natCast]
  exact N.earlier_stores k j.toNat a keys values n.toNat (by omega) (by omega)
    (by rw [N.integer_cast, N.integer_cast]; omega)

-- the lemmas of aggregation.dfy

theorem current_sums : Stmt.current_sums := by
  intro x values n hvalues; exact N.current_sums x values values.length rfl

theorem earlier_sums : Stmt.earlier_sums := by
  intro j x values n hvalues ⟨hj, hjn⟩
  rw [earlier_N_nonneg j _ hj, prefix_N]
  exact N.earlier_sums j.toNat x values n.toNat (by omega) (by rw [N.integer_cast, N.integer_cast]; omega)

theorem prefix_sums : Stmt.prefix_sums := by
  intro k x values n hvalues; rw [prefix_N, prefix_N]; exact N.prefix_sums k.toNat x values values.length rfl

theorem sum_empty : Stmt.sum_empty := N.sum_empty

theorem sum_consts : Stmt.sum_consts := by
  intro n x hn; rw [consts_N, N.sum_consts, N.integer_cast, Int.toNat_of_nonneg hn]

theorem sum_counter : Stmt.sum_counter := by
  intro i c n hn; rw [counter_N, N.sum_counter, N.integer_cast, Int.toNat_of_nonneg hn]

theorem counts_false : Stmt.counts_false := by
  intro x bs n hbs; exact N.counts_false x bs bs.length rfl

theorem counts_true : Stmt.counts_true := by
  intro x bs n hbs; exact N.counts_true x bs bs.length rfl

theorem current_trace_step_or_keep : Stmt.current_trace_step_or_keep := by
  intro x0 n a xs C hxs
  rw [counter_N]
  exact N.current_trace_step_or_keep_gen a C _ xs x0 (by rw [N.length_butlast_counter]; omega)

theorem current_trace_add_at : Stmt.current_trace_add_at := by
  intro α _ a k values n hvalues; exact N.current_trace_add_at a k values values.length rfl

theorem current_trace_histogram : Stmt.current_trace_histogram := by
  intro c0 a n hs v hhs; rw [counter_N]; exact N.current_trace_histogram c0 a n.toNat hs v (by omega)

theorem current_counts : Stmt.current_counts := by
  intro α _ x e vs n hvs; exact N.current_counts x e vs vs.length rfl

theorem earlier_counts : Stmt.earlier_counts := by
  intro α _ j x e vs n hvs ⟨hj, hjn⟩
  rw [earlier_N_nonneg j _ hj, prefix_N]
  exact N.earlier_counts j.toNat x e vs n.toNat (by omega) (by rw [N.integer_cast, N.integer_cast]; omega)

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
  intro α _ a k v keys n hkeys hd
  exact fold_selects_update 0 id sum rfl (fun _ _ => rfl) a k v keys hd

theorem parity_selects_update : Stmt.parity_selects_update := by
  intro α _ a k v keys n hkeys hd
  exact fold_selects_update 0 (fun w => if w % 2 = 0 then 1 else -1) parity rfl (fun _ _ => rfl) a k v keys hd

theorem count_selects_update : Stmt.count_selects_update := by
  intro α β _ _ a k w e keys n hkeys hd
  exact fold_selects_update 0 (fun u => if u = e then 1 else 0) (count e) rfl (fun _ _ => rfl) a k w keys hd


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

theorem sum_cases_below : Stmt.sum_cases_below := by
  intro n c d e P h
  rw [counter_N]
  apply N.sum_cases_below n.toNat c d e P
  rw [N.integer_cast]
  rcases Int.lt_or_le n 0 with hn | hn
  · rw [show n.toNat = 0 by omega]; simp only [Int.natCast_zero, Int.zero_mul]; omega
  · rw [Int.toNat_of_nonneg hn]; exact h

theorem sum_mod_below : Stmt.sum_mod_below := by
  intro n m e ⟨hn, h⟩
  rw [counter_N]; apply N.sum_mod_below n.toNat m e; rw [N.integer_cast, Int.toNat_of_nonneg hn]; exact h

theorem sum_neg : Stmt.sum_neg := by
  intro values n hvalues; exact N.sum_neg values values.length rfl

theorem sum_scale : Stmt.sum_scale := by
  intro values a n hvalues; exact N.sum_scale values a values.length rfl

theorem sum_add : Stmt.sum_add := by
  intro xs ys n hxs hys; exact N.sum_add xs ys xs.length rfl (by omega)

theorem sum_indicator_true : Stmt.sum_indicator_true := by
  intro α _ xs P n hxs; exact N.sum_indicator_true xs P xs.length rfl

theorem sum_indicator_false : Stmt.sum_indicator_false := by
  intro α _ xs P n hxs; exact N.sum_indicator_false xs P xs.length rfl

theorem count_consts : Stmt.count_consts := by
  intro α _ n e v hn; rw [consts_N, N.count_consts, N.integer_cast, Int.toNat_of_nonneg hn]

theorem count_true_below : Stmt.count_true_below := by
  intro m i n h
  rw [counter_N]; exact N.count_true_below m i n.toNat (by rw [N.integer_cast]; omega)

theorem count_true_above : Stmt.count_true_above := by
  intro m i n h
  rw [counter_N, N.count_true_above m i n.toNat (by rw [N.integer_cast]; omega), N.integer_cast]; omega

theorem count_nonnegative : Stmt.count_nonnegative := N.count_nonnegative

theorem count_remainder : Stmt.count_remainder := by
  intro n m r ⟨hn, h⟩
  rw [counter_N, N.count_remainder n.toNat m r h, N.integer_cast, Int.toNat_of_nonneg hn]

theorem count_false_true : Stmt.count_false_true := by
  intro i c n hs P hhs hn
  rw [counter_N, N.count_false_true i c n.toNat hs P (by omega), N.integer_cast, Int.toNat_of_nonneg hn]

theorem count_true_eq : Stmt.count_true_eq := by
  intro ks r hs F n hks hhs; exact N.count_true_eq ks r hs F ks.length rfl (by omega)

theorem current_maxs_initial : Stmt.current_maxs_initial := by
  intro x values n hvalues; exact N.current_maxs_initial x values values.length rfl

theorem current_maxs_earlier : Stmt.current_maxs_earlier := by
  intro k x values n hvalues ⟨hk, hkn⟩
  rw [earlier_N_nonneg k _ hk]
  exact N.current_maxs_earlier k.toNat x values n.toNat (by omega) (by rw [N.integer_cast, N.integer_cast]; omega)

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

theorem current_maxs_prefix_earlier : Stmt.current_maxs_prefix_earlier := by
  intro k x n xs hxs ⟨hk, hkn⟩
  rw [← earlier_prefix k n xs hkn]
  exact current_maxs_earlier k x («prefix» n xs) («prefix» n xs).length rfl
    ⟨hk, by rw [prefix_N]; have := lt_length_prefix k.toNat n.toNat xs (by omega) (by omega); omega⟩

theorem current_mins_initial : Stmt.current_mins_initial := by
  intro x values n hvalues; exact N.current_mins_initial x values values.length rfl

theorem current_mins_earlier : Stmt.current_mins_earlier := by
  intro k x values n hvalues ⟨hk, hkn⟩
  rw [earlier_N_nonneg k _ hk]
  exact N.current_mins_earlier k.toNat x values n.toNat (by omega) (by rw [N.integer_cast, N.integer_cast]; omega)

theorem current_mins_prefix_earlier : Stmt.current_mins_prefix_earlier := by
  intro k x n xs hxs ⟨hk, hkn⟩
  rw [← earlier_prefix k n xs hkn]
  exact current_mins_earlier k x («prefix» n xs) («prefix» n xs).length rfl
    ⟨hk, by rw [prefix_N]; have := lt_length_prefix k.toNat n.toNat xs (by omega) (by omega); omega⟩

theorem current_maxs_seeded_earlier : Stmt.current_maxs_seeded_earlier := by
  intro j h i n xs ⟨hh, hj1, hj2⟩
  by_cases e : j = h
  · subst e; exact N.current_maxs_initial _ _ _ rfl
  · rw [counter_N]
    have hr := N.current_maxs_earlier (j - i).toNat (earlier h xs)
      (maps (butlast (N.counter i 1 n.toNat)) (fun v => earlier v xs)) n.toNat
      (by rw [N.length_maps, N.length_butlast_counter]) (by rw [N.integer_cast, N.integer_cast]; omega)
    rwa [N.earlier_maps_counter _ _ _ _ (by omega), show i + ((j - i).toNat : Int) = j by omega] at hr

theorem current_mins_seeded_earlier : Stmt.current_mins_seeded_earlier := by
  intro j h i n xs ⟨hh, hj1, hj2⟩
  by_cases e : j = h
  · subst e; exact N.current_mins_initial _ _ _ rfl
  · rw [counter_N]
    have hr := N.current_mins_earlier (j - i).toNat (earlier h xs)
      (maps (butlast (N.counter i 1 n.toNat)) (fun v => earlier v xs)) n.toNat
      (by rw [N.length_maps, N.length_butlast_counter]) (by rw [N.integer_cast, N.integer_cast]; omega)
    rwa [N.earlier_maps_counter _ _ _ _ (by omega), show i + ((j - i).toNat : Int) = j by omega] at hr

-- compacts without the dead branch of its update, from the count 0 on
theorem compacts_N (c0 : Int → Int) (ks : List Int) (P : Int → Prop) : compacts c0 ks P = N.compacting P c0 0 ks := by
  simp only [compacts, N.compacting, N.ite_not_else]

theorem select_current_compacts_lower : Stmt.select_current_compacts_lower := by
  intro c0 K n m x P ⟨hK, hm, hx0, hxm⟩
  subst hK hm
  rw [counter_N] at hxm ⊢
  rw [compacts_N]
  have := (N.compacting_from P n.toNat 0 0 c0 x).2.2 ⟨hx0, by omega⟩
  omega

theorem select_current_compacts_upper : Stmt.select_current_compacts_upper := by
  intro c0 K n m x P ⟨hK, hm, hx0, hxm⟩
  subst hK hm
  rw [counter_N] at hxm ⊢
  rw [compacts_N]
  have h1 := (N.compacting_from P n.toNat 0 0 c0 x).1
  have := (N.compacting_from P n.toNat 0 0 c0 x).2.2 ⟨hx0, by omega⟩
  omega

theorem select_current_filters_above : Stmt.select_current_filters_above := by
  intro c0 ks b F m x n hks ⟨hm, hx0, hxm⟩
  rw [show filters_above c0 ks b F = N.filtering_above c0 0 ks b F by
    simp only [filters_above, N.filtering_above, N.ite_le_lt]]
  exact (N.filtering_above_from b F ks 0 c0 x).2 ⟨hx0, by omega⟩

theorem select_current_filters_below : Stmt.select_current_filters_below := by
  intro c0 K n b F m x ⟨hK, hm, hx0, hxm⟩
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
  intro x values n hvalues; exact N.current_parities x values values.length rfl

theorem select_current_trace_reset_add : Stmt.select_current_trace_reset_add := by
  intro a0 j n c G
  rw [counter_N, N.select_current_trace_reset_add]
  exact ite_iff (by show n.toNat = 0 ↔ _; omega) _ _

theorem select_current_trace_prefix_sums : Stmt.select_current_trace_prefix_sums := by
  intro b0 n j G
  rw [counter_N, counter_N, N.select_current_trace_prefix_sums, N.integer_cast, N.natural_eq, counter_N]
  by_cases h1 : 0 ≤ j ∧ j ≤ n
  · rw [if_pos (by omega), if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : 0 ≤ j ∧ j ≤ (n.toNat : Int)
    · rw [if_pos h2, show j = 0 by omega]; simp [N.counter, butlast, maps, sum]
    · rw [if_neg h2]

theorem select_current_trace_prefix_sums_add : Stmt.select_current_trace_prefix_sums_add := by
  intro b0 n j G H
  rw [counter_N, counter_N, N.select_current_trace_prefix_sums_add, N.integer_cast, N.natural_eq, counter_N]
  by_cases h1 : 0 ≤ j ∧ j ≤ n
  · rw [if_pos (by omega), if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : 0 ≤ j ∧ j ≤ (n.toNat : Int)
    · rw [if_pos h2, show j = 0 by omega]; simp [N.counter, butlast, maps, sum]
    · rw [if_neg h2]

theorem select_current_trace_recurrence : Stmt.select_current_trace_recurrence := by
  intro a0 n c j G
  rw [counter_N, N.select_current_trace_recurrence, N.integer_cast, N.natural_eq, counter_N]
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
theorem select_swap : Stmt.select_swap := N.select_swap
theorem perm_swap : Stmt.perm_swap := N.perm_swap

theorem perm_swaps_one : Stmt.perm_swaps_one := by
  intro a b ks P Q n hks; exact N.perm_swaps_one a b ks P Q ks.length rfl

theorem perm_swaps : Stmt.perm_swaps := by
  intro a b ks hs P Q n hks hhs; exact N.perm_swaps a b ks hs P Q ks.length rfl (by omega)

theorem perm_steps : Stmt.perm_steps := by
  intro a c ks F n hks; exact N.perm_steps a c ks F ks.length rfl

theorem perm_steps_two : Stmt.perm_steps_two := by
  intro a c ks is F n hks his; exact N.perm_steps_two a c ks is F ks.length rfl (by omega)

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
  intro a0 n c P G; rw [counter_N]; exact N.stores_cases a0 n.toNat c P G

theorem stores_index_cases : Stmt.stores_index_cases := by
  intro a0 n c d P; rw [counter_N]; exact N.stores_index_cases a0 n.toNat c d P

theorem stores_cases_point : Stmt.stores_cases_point := by
  intro a0 n c F
  simp only [N.ite_ne_eq]
  rw [← N.trace_stores_maps]
  congr 1
  funext a k j
  by_cases e : k = c
  · subst e; simp
  · simp [e]

theorem stores_read_unmodified : Stmt.stores_read_unmodified := by
  intro a0 n hs F hhs h
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n = m := ⟨hs.length, hhs.symm⟩
  simp only [counter_N, Int.toNat_natCast] at h ⊢
  exact N.stores_read_unmodified a0 m hs F (by omega) (by simp only [N.integer_cast]; exact h)

theorem select_current_trace_reset_keep : Stmt.select_current_trace_reset_keep := by
  intro a0 j n c
  rw [counter_N, N.select_current_trace_reset_keep]
  exact ite_iff (toNat_zero_iff n) _ _

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

theorem select_current_trace_shift : Stmt.select_current_trace_shift := by
  intro a i n j hn
  rw [counter_N, select_current_trace_shift_N, Int.toNat_of_nonneg hn]


theorem select_store_other : Stmt.select_store_other := N.select_store_other

theorem selects_stores_counter : Stmt.selects_stores_counter := by
  intro a i c n vs hvs; rw [counter_N]; exact N.selects_stores_counter a i c n.toNat vs (by omega)

theorem select_current_trace_conditional_store : Stmt.select_current_trace_conditional_store := by
  intro a0 n j C V
  rw [counter_N, N.select_current_trace_conditional_store, N.integer_cast]
  exact ite_iff ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩⟩ _ _

theorem select_current_trace_conditional_store_deps : Stmt.select_current_trace_conditional_store_deps := by
  intro a0 n j hs cs vs C V hhs hcs hvs
  rw [counter_N, N.select_current_trace_conditional_store_deps a0 n.toNat j hs cs vs C V (by omega) (by omega)
    (by omega), N.integer_cast, N.natural_eq]
  by_cases hj : 0 ≤ j
  · rw [earlier_N_nonneg j hs hj, earlier_N_nonneg j cs hj, earlier_N_nonneg j vs hj]
    exact ite_iff ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩⟩ _ _
  · rw [if_neg (fun h => hj h.1), if_neg (fun h => hj h.1)]

theorem select_current_trace_cap : Stmt.select_current_trace_cap := by
  intro a0 n j b
  rw [counter_N, N.select_current_trace_cap, N.integer_cast]
  exact ite_iff ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩⟩ _ _

theorem select_current_trace_copy_both_ends : Stmt.select_current_trace_copy_both_ends := by
  intro a0 b n m j
  rw [counter_N, N.copy_both_ends_from b m j n.toNat 0 a0]
  exact ite_iff (by omega) _ _

theorem select_current_trace_copy_both_ends_list : Stmt.select_current_trace_copy_both_ends_list := by
  intro a0 xs n m j hxs
  exact select_current_trace_copy_both_ends a0 (fun v => earlier v xs) n m j

theorem store_select_other : Stmt.store_select_other := N.store_select_other

-- the lemmas of counters.dfy

theorem trace_merge_cases_ne : Stmt.trace_merge_cases_ne := by
  intro x0 n c d F h; rw [counter_N]; exact N.trace_merge_cases_ne x0 n.toNat c d F h

theorem invs_two_phases : Stmt.invs_two_phases := by
  intro x0 n b c B h
  rw [counter_N, N.invs_two_phases x0 n.toNat b c B h, N.integer_cast]
  by_cases hn : n ≤ 0
  · exact ⟨fun _ => Or.inl hn, fun _ => Or.inl ((toNat_zero_iff n).mpr hn)⟩
  · rw [Int.toNat_of_nonneg (by omega)]
    constructor
    · rintro (h0 | h0)
      · exact absurd ((toNat_zero_iff n).mp h0) hn
      · exact Or.inr h0
    · rintro (h0 | h0)
      · exact absurd h0 hn
      · exact Or.inr h0

theorem invs_not_or : Stmt.invs_not_or := by
  intro hs gs fs P Q n hhs hgs hfs; exact N.invs_not_or hs gs fs P Q hs.length rfl (by omega) (by omega)

theorem current_trace_constant : Stmt.current_trace_constant := by
  intro α _ x y i c n
  rw [counter_N, N.current_trace_constant]
  exact ite_iff (toNat_zero_iff n) _ _

theorem current_trace_two_phases : Stmt.current_trace_two_phases := by
  intro x0 n b c ⟨hn, h⟩
  rw [counter_N, N.current_trace_two_phases x0 n.toNat b c h, N.integer_cast, Int.toNat_of_nonneg hn]

theorem current_trace_catch_up : Stmt.current_trace_catch_up := by
  intro y0 x0 n ⟨hn, h⟩
  rw [counter_N, counter_N, N.current_trace_catch_up y0 x0 n.toNat h, N.integer_cast, Int.toNat_of_nonneg hn]

theorem current_trace_flag : Stmt.current_trace_flag := by
  intro α _ x0 c n hs D hhs; rw [counter_N]; exact N.current_trace_flag x0 c n.toNat hs D (by omega)

theorem current_trace_increasing : Stmt.current_trace_increasing := by
  intro x0 n a b c hs C D E hhs ⟨hn, h⟩
  rw [counter_N]
  exact N.current_trace_increasing x0 n.toNat a b c hs C D E (by omega)
    ⟨fun h0 => absurd ((toNat_zero_iff n).mp h0) (by omega), h⟩

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

theorem select_current_trace_stride2 : Stmt.select_current_trace_stride2 := by
  intro a0 n X Y j
  rw [counter_N, N.select_current_trace_stride2, N.integer_cast]
  exact ite_iff (by omega) _ _

theorem select_current_trace_stride3 : Stmt.select_current_trace_stride3 := by
  intro a0 n X Y Z j
  rw [counter_N, N.select_current_trace_stride3, N.integer_cast]
  exact ite_iff (by omega) _ _

theorem select_current_trace_stride2_cases : Stmt.select_current_trace_stride2_cases := by
  intro a0 n P Q R X1 Y1 X2 Y2 X3 Y3 j h
  rw [counter_N, N.select_current_trace_stride2_cases a0 n.toNat P Q R X1 Y1 X2 Y2 X3 Y3 j h, N.integer_cast]
  exact ite_iff (by omega) _ _

-- no steps leave the array as it is, where neither condition holds
theorem select_current_trace_ahead : Stmt.select_current_trace_ahead := by
  intro a0 n m F G j h
  rw [counter_N]
  rcases Int.lt_or_le n 0 with hn | hn
  · rw [show n.toNat = 0 by omega, if_neg (by omega), if_neg (by omega)]; rfl
  · rw [N.select_current_trace_ahead a0 n.toNat m F G j (by rw [N.integer_cast]; omega), N.integer_cast,
      Int.toNat_of_nonneg hn]

theorem select_current_trace_ahead_down : Stmt.select_current_trace_ahead_down := by
  intro a0 n s F G j
  rw [counter_N, counter_N, N.select_current_trace_ahead_down, N.integer_cast]
  rcases Int.lt_or_le n 0 with hn | hn
  · rw [show n.toNat = 0 by omega, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [Int.toNat_of_nonneg hn]

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

theorem current_series : Stmt.current_series := by
  intro x0 z a n; rw [series_N, pow_N]; exact N.current_series x0 z a n.toNat

end TEQ
