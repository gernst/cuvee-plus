-- the lemmas without the premises that the contexts of the goals of -teq provide (premises.txt, the hypotheses on
-- lengths) are false: counterexamples
import TEQ.Proofs

open Classical

set_option linter.unusedVariables false

namespace TEQ

open Nat (zero succ)
open List (nil cons length)

-- prefix_counter and prefix_consts for k > n, where the prefix is as long as the list
example : ¬ («prefix» 1 (butlast (counter 0 1 0)) = butlast (counter 0 1 1)) :=
  by simp [«prefix», counter, butlast]

example : ¬ («prefix» 1 (butlast (consts 0 (0 : Int))) = butlast (consts 1 0)) :=
  by simp [«prefix», consts, butlast]

-- maps_earlier for a list that is longer than the iterations
example : ¬ (maps (butlast (counter 0 1 0)) (fun k => earlier (natural k) [(1 : Int)]) = [1]) :=
  by simp [maps, counter, butlast]

-- the following hold only for dependencies of equal length (see bugs.md), here a further dependency that is shorter
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

-- agree_prefix_def
example : ¬ (invs (List.zip (butlast (counter 0 1 1)) ([] : List Int))
      (fun ⟨k, h⟩ => earlier (natural k) [(1 : Int)] = earlier (natural k) [2])
    ↔ agree_prefix 1 [1] [2]) :=
  by simp [invs, agree_prefix, earlier]

-- not_occurs_prefix
example : ¬ (invs (List.zip (butlast (counter 0 1 1)) ([] : List Int)) (fun ⟨k, h⟩ => earlier (natural k) [(1 : Int)] ≠ 1)
    ↔ ¬occurs 1 («prefix» 1 [(1 : Int)])) :=
  by simp [invs, occurs, «prefix»]

-- above_iterations_def
example : ¬ (invs (List.zip (butlast (counter 0 1 1)) (List.zip ([] : List Int) [(0 : Int)])) (fun ⟨k, h, t⟩ => k < t)
    ↔ above_iterations 1 [0]) :=
  by simp [invs, above_iterations, earlier, integer]

-- select_current_trace_cap
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

-- select_current_trace_conditional_store_deps
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
