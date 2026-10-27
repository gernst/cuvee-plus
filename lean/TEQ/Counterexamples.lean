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
example : ¬ (sum (maps (List.zip [(1 : Int)] ([] : List Int)) (fun ⟨v, w⟩ => v + w)) = sum [1] + sum []) :=
  by simp [maps, sum]

-- count_false_true
example : ¬ (count False (maps (List.zip (butlast (counter 0 1 1)) ([] : List Int)) (fun ⟨k, h⟩ => k < h))
    = 1 - count True (maps (List.zip (butlast (counter 0 1 1)) ([] : List Int)) (fun ⟨k, h⟩ => k < h))) :=
  by simp [maps, count, counter, butlast]

-- current_trace_increasing
example : ¬ ((0 : Int) < 1 ∧ (0 : Int) < 1 ∧ (0 : Int) < 1 ∧ (0 : Int) < 1
    → (0 : Int) < current (trace 0 (List.zip (butlast (counter 0 1 1)) ([] : List Int))
        (fun x ⟨k, h⟩ => if h < 0 then x + 1 else if h = 0 then x + 1 else x + 1))) :=
  by simp [trace, current]

-- selects_stores and selects_stores_counter, with fewer values than keys
example : ¬ (distincts [(0 : Int)] → selects (current (stores (fun (_ : Int) => (0 : Int)) [0] [])) [0] = []) :=
  by simp [distincts, occurs, selects, maps, stores, trace, current]

-- select_current_trace_conditional_store_deps
example : ¬ (current (trace (fun (_ : Int) => (0 : Int)) (List.zip (butlast (counter 0 1 1)) (List.zip ([] : List Int) (List.zip ([] : List Int) ([] : List Int))))
      (fun a ⟨k, h, c, v⟩ => if True then fun j => if j = k then 1 else a j else a)) 0
    = (if 0 ≤ (0 : Int) ∧ (0 : Int) < 1 ∧ True then 1 else 0)) :=
  by simp [trace, current]

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

-- the conditions 0 ≤ n of lemmas whose closed forms hold for the counts of loops only: a count that is not positive
-- is no step, as in the definitions over integers, where the closed form is that of a negative number of steps

-- sum_mod_below, where the bound of the sum is negative
example : ¬ (0 < (2 : Int) ∧ (-1 : Int) * (2 - 1) ≤ -1
    → sum (maps (butlast (counter 0 1 (-1))) (fun k => if 0 < k then k % 2 else 0)) ≤ -1) :=
  by simp [counter, butlast, maps, sum]

-- current_mods_up and current_mods, where the counter goes back from i
example : ¬ (0 ≤ (0 : Int) + (-1) * (-1) ∧ (0 : Int) + (-1) * (-1) < 5
    → current (mods 0 (-1) 5 (-1)) = 0 + (-1) * (-1)) :=
  by simp [mods, counter, butlast, trace, current]

example : ¬ (0 ≤ (0 : Int) ∧ (0 : Int) < 5 → current (mods 0 1 5 (-1)) = (0 + (-1) * 1) % 5) :=
  by simp [mods, counter, butlast, trace, current]

end TEQ
