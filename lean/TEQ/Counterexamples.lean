-- the lemmas without the premises that the contexts of the goals of -teq provide (premises.txt, the hypotheses on
-- lengths) are false: counterexamples
import TEQ.Proofs

open Classical

set_option linter.unusedVariables false

namespace TEQ

open List (nil cons length)

-- prefix_counter and prefix_consts for k > n, where the prefix is as long as the list
example : ¬ («prefix» 1 (butlast (counter 0 1 0)) = butlast (counter 0 1 1)) :=
  by simp [«prefix», counter, butlast]

example : ¬ («prefix» 1 (butlast (consts 0 (0 : Int))) = butlast (consts 1 0)) :=
  by simp [«prefix», consts, butlast]

-- prefix_phases for k > n
example : ¬ («prefix» 1 (butlast (phases 0 0 0 (fun x _ => x) (fun x _ => x)))
    = butlast (phases 0 0 1 (fun x _ => x) (fun x _ => x))) :=
  by simp [«prefix», phases, iterations, butlast, trace]

-- the former maps_earlier, whose right-hand side was the whole list, for a list that is longer than the iterations,
-- e.g. that of an earlier loop with more iterations (bugs.md); maps_earlier has its prefix now
example : ¬ (maps (butlast (counter 0 1 0)) (fun k => earlier k [(1 : Int)]) = [1]) :=
  by simp [maps, counter, butlast]

-- earlier_eq_not_occurs_prefix for a list shorter than the prefix, whose read beyond its end is unspecified, which
-- may be the value that does not occur in the prefix
example : ¬ (¬occurs (unspecified : Int) («prefix» 1 ([] : List Int)) ∧ (0 : Int) ≤ 0 ∧ (0 : Int) < 1
    → (earlier 0 ([] : List Int) = unspecified ↔ False)) :=
  by simp [occurs, «prefix», earlier]

-- the following hold only for dependencies of equal length (see bugs.md), here a further dependency that is shorter
-- than the iterations, which zip truncates

-- sum_add
example : ¬ (sum (elems (maps (List.zip [(1 : Int)] ([] : List Int)) (fun ⟨v, w⟩ => v + w)))
    = sum (elems [1]) + sum (elems [])) :=
  by simp [maps, sum_N, N.sum]

-- count_false_true
example : ¬ (Bag.count (elems (maps (List.zip (butlast (counter 0 1 1)) ([] : List Int)) (fun ⟨k, h⟩ => k < h))) False
    = 1 - Bag.count (elems (maps (List.zip (butlast (counter 0 1 1)) ([] : List Int)) (fun ⟨k, h⟩ => k < h))) True) :=
  by simp [maps, count_N, N.count, counter, butlast]

-- selects_stores and selects_stores_counter, with fewer values than keys
example : ¬ (distincts [(0 : Int)] → selects (current (stores (fun (_ : Int) => (0 : Int)) [0] [])) [0] = []) :=
  by simp [distincts, occurs, selects, maps, stores, trace, current]

-- length_stores_where and prefix_stores_where, with guards and values shorter than the iterations, which the fold
-- over the counter does not see (premises.txt)
example : ¬ ((length (butlast (stores_where (fun (_ : Int) => (0 : Int)) 0 1 1 [] [])) : Int) = 1) :=
  by simp [stores_where, counter, butlast, trace]

example : ¬ («prefix» 1 (butlast (stores_where (fun (_ : Int) => (0 : Int)) 0 1 0 [True] [1]))
    = butlast (stores_where (fun (_ : Int) => (0 : Int)) 0 1 1 («prefix» 1 [True]) («prefix» 1 [1]))) :=
  by simp [stores_where, «prefix», counter, butlast, trace]

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

-- earlier_bands (and earlier_bors, earlier_bxors) at a negative position, where the read is unspecified and the prefix is empty,
-- whose aggregate is the neutral element: the initial value would be unspecified, whatever it is
example : ¬ ∀ x : Int, earlier (-1) (butlast (bands x [])) = bitand x (band (elems («prefix» (-1) ([] : List Int)))) := by
  intro h
  have h0 := h 0
  have h1 := h 1
  simp only [bands, trace, butlast, «prefix», band_N, List.foldr_nil, bitand_neg_one] at h0 h1
  rw [h0] at h1; contradiction

-- band_seed_earlier and bor_seed_earlier (and bxor_seed_earlier, as bor_seed_earlier) for a list shorter than the
-- reads, whose read beyond its end is unspecified: each holds exactly if that is its neutral element, all ones for band
-- and zero for bor and bxor, hence not both
example : ¬ ((bitand (earlier 0 ([] : List Int))
        (band (elems (maps (butlast (counter 0 1 0)) (fun k => earlier (k + 1) ([] : List Int))))))
      = band (elems («prefix» (0 + 1) ([] : List Int)))
    ∧ (bitor (earlier 0 ([] : List Int))
        (bor (elems (maps (butlast (counter 0 1 0)) (fun k => earlier (k + 1) ([] : List Int))))))
      = bor (elems («prefix» (0 + 1) ([] : List Int)))) := by
  intro ⟨h1, h2⟩
  rw [band_N, band_N] at h1
  rw [bor_N, bor_N] at h2
  have hc : butlast (counter 0 1 0) = [] := by rw [counter_N]; rfl
  simp only [hc, maps, «prefix», List.foldr_nil, bitand_neg_one, bitor_zero] at h1 h2
  rw [h1] at h2; contradiction

-- select_current_tiles for an inner loop with fewer values than iterations, which zip truncates: the cell keeps its
-- initial value, the right-hand side reads beyond the end of the values
example : ¬ ∀ (a0 : Int → Int), current (trace a0 (List.zip (butlast (counter 0 1 1)) [(0 : Int)])
      (fun b ⟨k, h⟩ => current (stores b (maps (butlast (counter 0 1 1)) (fun l => l + 1 * k)) ([] : List Int)))) 0
    = (if 0 ≤ (0 : Int) ∧ (0 : Int) < 1 * 1 then earlier (0 % 1) ([] : List Int) else a0 0) := by
  intro h
  have h0 := h (fun _ => 0)
  have h1 := h (fun _ => 1)
  simp [counter, butlast, maps, stores, trace, current, earlier] at h0 h1
  rw [← h0] at h1; contradiction

-- the conditions 0 ≤ n of lemmas whose closed forms hold for the counts of loops only: a count that is not positive
-- is no step, as in the definitions over integers, where the closed form is that of a negative number of steps

-- sum_mod_below, where the bound of the sum is negative
example : ¬ (0 < (2 : Int) ∧ (-1 : Int) * (2 - 1) ≤ -1
    → sum (elems (maps (butlast (counter 0 1 (-1))) (fun k => if 0 < k then k % 2 else 0))) ≤ -1) :=
  by simp [counter, butlast, maps, sum_N, N.sum]

-- current_mods_up and current_mods, where the counter goes back from i
example : ¬ (0 ≤ (0 : Int) + (-1) * (-1) ∧ (0 : Int) + (-1) * (-1) < 5
    → current (mods 0 (-1) 5 (-1)) = 0 + (-1) * (-1)) :=
  by simp [mods, counter, butlast, trace, current]

example : ¬ (0 ≤ (0 : Int) ∧ (0 : Int) < 5 → current (mods 0 1 5 (-1)) = (0 + (-1) * 1) % 5) :=
  by simp [mods, counter, butlast, trace, current]

end TEQ
