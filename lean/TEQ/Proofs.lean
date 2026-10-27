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

-- the reset and the guarded additions: after the reset at the iteration 0, each later iteration adds G k where P k holds
-- and keeps the array otherwise
theorem reset_add_keep_later (j c : Int) (P : Int → Prop) (G : Int → Int) (m : Nat) : ∀ (s : Int) (x : Int → Int), 1 ≤ s →
    current (trace x (butlast (N.counter s 1 m))
      (fun a k =>
        if k = 0 then fun j1 => if j1 = j then c else a j1
        else if 0 < k ∧ P k then fun j1 => if j1 = j then a j + G k else a j1
        else if 0 < k ∧ ¬P k then a else unspecified)) j
      = x j + sum (maps (butlast (N.counter s 1 m)) (fun k => if 0 < k then if P k then G k else 0 else 0)) := by
  induction m with
  | zero => intro s x hs; simp [N.counter, butlast, trace, current, maps, sum]
  | succ m ih =>
    intro s x hs
    rw [N.butlast_counter_succ, N.trace_cons, N.current_step_eq, ih (s + 1) _ (by omega)]
    simp only [maps, sum, if_neg (show ¬s = 0 by omega), if_pos (show 0 < s by omega)]
    by_cases hp : P s
    · simp only [hp, and_true, not_true_eq_false, and_false, if_pos (show 0 < s by omega), ↓reduceIte, eq_self]; omega
    · simp only [hp, and_true, not_false_eq_true, and_false, if_pos (show 0 < s by omega), ↓reduceIte]; omega

theorem select_current_trace_reset_add_keep : Stmt.select_current_trace_reset_add_keep := by
  intro a0 j n c P G
  rw [counter_N]
  by_cases hn : n ≤ 0
  · rw [if_pos hn, show n.toNat = 0 by omega]; rfl
  · rw [if_neg hn, show n.toNat = n.toNat - 1 + 1 by omega, N.butlast_counter_succ, N.trace_cons, N.current_step_eq,
      reset_add_keep_later j c P G _ (0 + 1) _ (by omega)]
    simp only [maps, sum, ↓reduceIte, Int.lt_irrefl]
    omega

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
-- strides of s positions per iteration, with values V d r at the offset r of the iteration of the dependency d: the
-- read at j is that of the iteration j / s at the offset j % s, by induction over the remaining iterations from t

theorem emod_of_block (s t j : Int) (h1 : s * t ≤ j) (h2 : j < s * t + s) : j % s = j - s * t := by
  have e : j = (j - s * t) + s * t := by omega
  rw [e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem ediv_of_block (s t j : Int) (hs : 0 < s) (h1 : s * t ≤ j) (h2 : j < s * t + s) : j / s = t := by
  have e : j = (j - s * t) + s * t := by omega
  rw [e, Int.add_mul_ediv_left _ _ (by omega), Int.ediv_eq_zero_of_lt (by omega) (by omega)]; omega

theorem stride_from {β : Type} [Inhabited β] (s : Int) (hs : 0 < s) (V : β → Int → Int)
    (U : (Int → Int) → Int × β → Int → Int)
    (hU : ∀ a k d i, U a (k, d) i = if s * k ≤ i ∧ i < s * k + s then V d (i - s * k) else a i) (j : Int) (r : Nat) :
    ∀ (b : Int → Int) (t : Int) (ds : List β), ds.length = r →
    current (trace b (List.zip (butlast (N.counter t 1 r)) ds) U) j
      = if s * t ≤ j ∧ j < s * t + s * r then V (N.earlier (j / s - t).toNat ds) (j % s) else b j := by
  induction r with
  | zero => intro b t ds hds; simp only [N.counter, butlast, List.zip_nil_left, N.current_trace_nil]; rw [if_neg (by omega)]
  | succ r ih =>
    intro b t ds hds
    cases ds with
    | nil => simp at hds
    | cons d ds =>
      rw [N.butlast_counter_succ, List.zip_cons_cons, N.trace_cons, N.current_step_eq, ih _ _ ds (by simp at hds; omega),
        hU]
      have hm : s * (t + 1) = s * t + s := by rw [Int.mul_add, Int.mul_one]
      have hr2 : s * ((r + 1 : Nat) : Int) = s * r + s := by rw [Int.natCast_add, Int.mul_add]; simp
      rw [hr2]
      have hsr : 0 ≤ s * (r : Int) := Int.mul_nonneg (by omega) (by omega)
      by_cases h1 : s * (t + 1) ≤ j ∧ j < s * (t + 1) + s * r
      · have hq : j / s - t = ((j / s - (t + 1)).toNat + 1 : Nat) := by
          have : t + 1 ≤ j / s := by
            have := Int.le_ediv_of_mul_le hs (show (t + 1) * s ≤ j by rw [Int.mul_comm]; omega)
            exact this
          omega
        rw [if_pos h1, if_pos (by omega), hq, Int.toNat_natCast]; rfl
      · rw [if_neg h1]
        by_cases h2 : s * t ≤ j ∧ j < s * t + s
        · rw [if_pos h2, if_pos (by omega), emod_of_block s t j h2.1 h2.2, ediv_of_block s t j hs h2.1 h2.2,
            Int.sub_self, show (0 : Int).toNat = 0 from rfl]; rfl
        · rw [if_neg h2, if_neg (by omega)]

theorem stride_read {β : Type} [Inhabited β] (s : Int) (hs : 0 < s) (V : β → Int → Int)
    (U : (Int → Int) → Int × β → Int → Int)
    (hU : ∀ a k d i, U a (k, d) i = if s * k ≤ i ∧ i < s * k + s then V d (i - s * k) else a i)
    (a0 : Int → Int) (n j : Int) (ds : List β) (hds : ds.length = n) :
    current (trace a0 (List.zip (butlast (counter 0 1 n)) ds) U) j
      = if 0 ≤ j ∧ j < s * n then V (earlier (j / s) ds) (j % s) else a0 j := by
  rw [counter_N, stride_from s hs V U hU j n.toNat a0 0 ds (by omega), Int.mul_zero, Int.zero_add,
    Int.toNat_of_nonneg (by omega : (0 : Int) ≤ n), Int.sub_zero]
  by_cases h : 0 ≤ j ∧ j < s * n
  · rw [if_pos h, if_pos h, earlier_N_nonneg _ _ (Int.ediv_nonneg h.1 (by omega))]
  · rw [if_neg h, if_neg h]

-- the version over the counter alone, whose values are the dependency
theorem stride_read_counter (s : Int) (hs : 0 < s) (V : Int → Int)
    (U : (Int → Int) → Int → Int → Int)
    (hU : ∀ a k i, U a k i = if s * k ≤ i ∧ i < s * k + s then V (i - s * k) else a i)
    (a0 : Int → Int) (n j : Int) :
    current (trace a0 (butlast (counter 0 1 n)) U) j = if 0 ≤ j ∧ j < s * n then V (j % s) else a0 j := by
  by_cases hn : n ≤ 0
  · rw [counter_N, show n.toNat = 0 by omega]; simp only [N.counter, butlast, N.current_trace_nil]
    rw [if_neg]; intro h; have : s * n ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hn; omega
  · have h := stride_read s hs (fun (_ : Int) r => V r) (fun a kd => U a kd.1) (fun a k d i => hU a k i) a0 n j
      (butlast (counter 0 1 n)) (by rw [counter_N, N.length_butlast_counter]; omega)
    rw [counter_N, N.trace_zip_self] at h
    rw [counter_N]; exact h

-- the blocks of the strides 3, 4, 5: the nested stores of an iteration (blk) as one read by the offset (off)
def blk3 (X0 X1 X2 : Int) (a : Int → Int) (k : Int) : Int → Int :=
  fun j => if j = 3 * k + 2 then X2 else (fun j => if j = 3 * k + 1 then X1 else
    (fun j => if j = 3 * k then X0 else a j) j) j

def off3 (X0 X1 X2 : Int) (r : Int) : Int := if r = 0 then X0 else if r = 1 then X1 else X2

theorem stride3_block (X0 X1 X2 : Int) : ∀ (a : Int → Int) (k i : Int),
    blk3 X0 X1 X2 a k i = if 3 * k ≤ i ∧ i < 3 * k + 3 then off3 X0 X1 X2 (i - 3 * k) else a i := by
  intro a k i; simp only [blk3, off3]; (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)

def blk4 (X0 X1 X2 X3 : Int) (a : Int → Int) (k : Int) : Int → Int :=
  fun j => if j = 4 * k + 3 then X3 else (fun j => if j = 4 * k + 2 then X2 else (fun j => if j = 4 * k + 1 then X1
    else (fun j => if j = 4 * k then X0 else a j) j) j) j

def off4 (X0 X1 X2 X3 : Int) (r : Int) : Int := if r = 0 then X0 else if r = 1 then X1 else if r = 2 then X2 else X3

theorem stride4_block (X0 X1 X2 X3 : Int) : ∀ (a : Int → Int) (k i : Int),
    blk4 X0 X1 X2 X3 a k i = if 4 * k ≤ i ∧ i < 4 * k + 4 then off4 X0 X1 X2 X3 (i - 4 * k) else a i := by
  intro a k i; simp only [blk4, off4]; (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)

def blk5 (X0 X1 X2 X3 X4 : Int) (a : Int → Int) (k : Int) : Int → Int :=
  fun j => if j = 5 * k + 4 then X4 else (fun j => if j = 5 * k + 3 then X3 else (fun j => if j = 5 * k + 2 then X2
    else (fun j => if j = 5 * k + 1 then X1 else (fun j => if j = 5 * k then X0 else a j) j) j) j) j

def off5 (X0 X1 X2 X3 X4 : Int) (r : Int) : Int :=
  if r = 0 then X0 else if r = 1 then X1 else if r = 2 then X2 else if r = 3 then X3 else X4

theorem stride5_block (X0 X1 X2 X3 X4 : Int) : ∀ (a : Int → Int) (k i : Int),
    blk5 X0 X1 X2 X3 X4 a k i = if 5 * k ≤ i ∧ i < 5 * k + 5 then off5 X0 X1 X2 X3 X4 (i - 5 * k) else a i := by
  intro a k i; simp only [blk5, off5]; (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)

-- the cases are conditions on the context, not on the iteration: in each, the update is one block
theorem select_current_trace_stride3_cases4 : Stmt.select_current_trace_stride3_cases4 := by
  intro a0 n P1 P2 P3 P4 X1_0 X1_1 X1_2 X2_0 X2_1 X2_2 X3_0 X3_1 X3_2 X4_0 X4_1 X4_2 j hP
  by_cases h1 : P1
  · simp only [h1, ↓reduceIte]; exact stride_read_counter 3 (by decide) (off3 X1_0 X1_1 X1_2) (blk3 X1_0 X1_1 X1_2) (stride3_block X1_0 X1_1 X1_2) a0 n j
  by_cases h2 : P2
  · simp only [h1, h2, ↓reduceIte]; exact stride_read_counter 3 (by decide) (off3 X2_0 X2_1 X2_2) (blk3 X2_0 X2_1 X2_2) (stride3_block X2_0 X2_1 X2_2) a0 n j
  by_cases h3 : P3
  · simp only [h1, h2, h3, ↓reduceIte]
    exact stride_read_counter 3 (by decide) (off3 X3_0 X3_1 X3_2) (blk3 X3_0 X3_1 X3_2) (stride3_block X3_0 X3_1 X3_2) a0 n j
  have h4 : P4 := hP.2 ⟨h1, h2, h3⟩
  simp only [h1, h2, h3, h4, ↓reduceIte]
  exact stride_read_counter 3 (by decide) (off3 X4_0 X4_1 X4_2) (blk3 X4_0 X4_1 X4_2) (stride3_block X4_0 X4_1 X4_2) a0 n j

theorem select_current_trace_stride4_cases5 : Stmt.select_current_trace_stride4_cases5 := by
  intro a0 n P1 P2 P3 P4 P5 X1_0 X1_1 X1_2 X1_3 X2_0 X2_1 X2_2 X2_3 X3_0 X3_1 X3_2 X3_3 X4_0 X4_1 X4_2 X4_3
    X5_0 X5_1 X5_2 X5_3 j hP
  by_cases h1 : P1
  · simp only [h1, ↓reduceIte]
    exact stride_read_counter 4 (by decide) (off4 X1_0 X1_1 X1_2 X1_3) (blk4 X1_0 X1_1 X1_2 X1_3) (stride4_block X1_0 X1_1 X1_2 X1_3) a0 n j
  by_cases h2 : P2
  · simp only [h1, h2, ↓reduceIte]
    exact stride_read_counter 4 (by decide) (off4 X2_0 X2_1 X2_2 X2_3) (blk4 X2_0 X2_1 X2_2 X2_3) (stride4_block X2_0 X2_1 X2_2 X2_3) a0 n j
  by_cases h3 : P3
  · simp only [h1, h2, h3, ↓reduceIte]
    exact stride_read_counter 4 (by decide) (off4 X3_0 X3_1 X3_2 X3_3) (blk4 X3_0 X3_1 X3_2 X3_3) (stride4_block X3_0 X3_1 X3_2 X3_3) a0 n j
  by_cases h4 : P4
  · simp only [h1, h2, h3, h4, ↓reduceIte]
    exact stride_read_counter 4 (by decide) (off4 X4_0 X4_1 X4_2 X4_3) (blk4 X4_0 X4_1 X4_2 X4_3) (stride4_block X4_0 X4_1 X4_2 X4_3) a0 n j
  have h5 : P5 := hP.2 ⟨h1, h2, h3, h4⟩
  simp only [h1, h2, h3, h4, h5, ↓reduceIte]
  exact stride_read_counter 4 (by decide) (off4 X5_0 X5_1 X5_2 X5_3) (blk4 X5_0 X5_1 X5_2 X5_3) (stride4_block X5_0 X5_1 X5_2 X5_3) a0 n j

theorem select_current_trace_stride5_cases6 : Stmt.select_current_trace_stride5_cases6 := by
  intro a0 n P1 P2 P3 P4 P5 P6 X1_0 X1_1 X1_2 X1_3 X1_4 X2_0 X2_1 X2_2 X2_3 X2_4 X3_0 X3_1 X3_2 X3_3 X3_4
    X4_0 X4_1 X4_2 X4_3 X4_4 X5_0 X5_1 X5_2 X5_3 X5_4 X6_0 X6_1 X6_2 X6_3 X6_4 j hP
  by_cases h1 : P1
  · simp only [h1, ↓reduceIte]
    exact stride_read_counter 5 (by decide) (off5 X1_0 X1_1 X1_2 X1_3 X1_4) (blk5 X1_0 X1_1 X1_2 X1_3 X1_4) (stride5_block X1_0 X1_1 X1_2 X1_3 X1_4) a0 n j
  by_cases h2 : P2
  · simp only [h1, h2, ↓reduceIte]
    exact stride_read_counter 5 (by decide) (off5 X2_0 X2_1 X2_2 X2_3 X2_4) (blk5 X2_0 X2_1 X2_2 X2_3 X2_4) (stride5_block X2_0 X2_1 X2_2 X2_3 X2_4) a0 n j
  by_cases h3 : P3
  · simp only [h1, h2, h3, ↓reduceIte]
    exact stride_read_counter 5 (by decide) (off5 X3_0 X3_1 X3_2 X3_3 X3_4) (blk5 X3_0 X3_1 X3_2 X3_3 X3_4) (stride5_block X3_0 X3_1 X3_2 X3_3 X3_4) a0 n j
  by_cases h4 : P4
  · simp only [h1, h2, h3, h4, ↓reduceIte]
    exact stride_read_counter 5 (by decide) (off5 X4_0 X4_1 X4_2 X4_3 X4_4) (blk5 X4_0 X4_1 X4_2 X4_3 X4_4) (stride5_block X4_0 X4_1 X4_2 X4_3 X4_4) a0 n j
  by_cases h5 : P5
  · simp only [h1, h2, h3, h4, h5, ↓reduceIte]
    exact stride_read_counter 5 (by decide) (off5 X5_0 X5_1 X5_2 X5_3 X5_4) (blk5 X5_0 X5_1 X5_2 X5_3 X5_4) (stride5_block X5_0 X5_1 X5_2 X5_3 X5_4) a0 n j
  have h6 : P6 := hP.2 ⟨h1, h2, h3, h4, h5⟩
  simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte]
  exact stride_read_counter 5 (by decide) (off5 X6_0 X6_1 X6_2 X6_3 X6_4) (blk5 X6_0 X6_1 X6_2 X6_3 X6_4) (stride5_block X6_0 X6_1 X6_2 X6_3 X6_4) a0 n j

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

-- the defaults: each iteration writes the positions 2 k and 2 k + 1 from its values x, y, z
theorem select_current_trace_stride2_defaults : Stmt.select_current_trace_stride2_defaults := by
  intro a0 n c d xs ys zs j hxs hys hzs
  have hl : (List.zip xs (List.zip ys zs)).length = n := by
    rw [N.length_zip_eq xs _ xs.length rfl (by rw [N.length_zip_eq ys zs ys.length rfl (by omega)]; omega)]; omega
  rw [stride_read 2 (by decide)
    (fun (t : Int × Int × Int) r => if r = 0 then (if t.1 ≠ c then t.1 else d)
      else if t.1 ≠ c then (if t.2.1 ≠ c then t.2.1 else d) else (if t.2.2 ≠ c then t.2.2 else d))
    _ (fun a k t i => by obtain ⟨x, y, z⟩ := t; dsimp only; (repeat' (split <;> try dsimp only)) <;> first | rfl | contradiction | omega | (congr 1; omega)) a0 n j _ hl]
  by_cases h : 0 ≤ j ∧ j < 2 * n
  · have hq : 0 ≤ j / 2 := Int.ediv_nonneg h.1 (by decide)
    rw [if_pos h, if_pos h, earlier_zip xs _ (j / 2) hq (by omega) (by rw [N.length_zip_eq ys zs ys.length rfl (by omega)]; omega),
      earlier_zip ys zs (j / 2) hq (by omega) (by omega)]
  · rw [if_neg h, if_neg h]

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
