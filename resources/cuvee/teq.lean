/-
The semantics of the lemma database of -teq (teq.dfy) in Lean 4, without Mathlib: the functions that teq.dfy only
declares are defined here, the functions that it defines and its lemmas are printed by
`./Cuvee.sh -print lean resources/cuvee/teq.dfy`, the lemmas as theorems to be proved, most of them still `sorry`.

Traces are the datatype of teq.dfy, which starts with a value (stop) and adds a value at its end in each step
(step), hence a trace is never empty; sequences are lists, arrays are functions. There is a single combinator of each kind, trace, maps, and
invs, over a single dependency: several dependencies are zipped into a list of tuples, which truncates them to the
shortest one, whereas the dependencies of the combinators of Cuvée have equal lengths, which teq.dfy does not state
(see TODO.md); `case φ => e case ψ => f` updates are conditionals (the guards are disjoint and complete).
Check with `lean resources/cuvee/teq.lean` (Lean 4.34).
-/
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace TEQ

-- the traces of trace equation systems, the values of a variable at the loop head (from teq.dfy)
inductive Trace (α₀ : Type) where
  | stop (first : α₀) : Trace α₀
  | step (prev : Trace α₀) (last : α₀) : Trace α₀

open Trace

axiom Trace_first {α₀ : Type} : Trace α₀ → α₀

axiom Trace_first_stop {α₀ : Type} (x₀ : α₀) : Trace_first (stop x₀) = x₀

axiom Trace_prev {α₀ : Type} : Trace α₀ → Trace α₀

axiom Trace_prev_step {α₀ : Type} (x₀ : Trace α₀) (x₁ : α₀) :
  Trace_prev (step x₀ x₁) = x₀

axiom Trace_last {α₀ : Type} : Trace α₀ → α₀

axiom Trace_last_step {α₀ : Type} (x₀ : Trace α₀) (x₁ : α₀) :
  Trace_last (step x₀ x₁) = x₁

-- the last element of a trace
def current {α₀ : Type} (x₀ : Trace α₀) : α₀ :=
  match x₀ with
  | .stop x => x
  | .step _ x => x

-- all but the last element of a trace, written ⌊X⌋
def butlast {α₀ : Type} (x₀ : Trace α₀) : List α₀ :=
  match x₀ with
  | .stop _ => []
  | .step xs _ => butlast xs ++ [current xs]

-- counter(i, c, n) is the trace i, i + c, ..., i + n c of n steps (the trace i if n <= 0)
def counter (i c n : Int) : Trace Int :=
  if n ≤ 0 then .stop i else .step (counter i c (n - 1)) (i + c * n)
termination_by n.toNat
decreasing_by omega

-- the elements of sequences
def earlier {α : Type} [Inhabited α] (k : Int) (xs : List α) : α :=
  xs.getD k.toNat default

-- the combinators: the trace of the accumulator, which starts with x and is updated by f with the values of the
-- dependency in turn, the sequence of the updates of these values, and the invariant of these values
def traceFrom {α β : Type} (f : α → β → α) : Trace α → List β → Trace α
  | xs, [] => xs
  | xs, d :: ds => traceFrom f (.step xs (f (current xs) d)) ds

def trace {α β : Type} (x : α) (ds : List β) (f : α → β → α) : Trace α :=
  traceFrom f (.stop x) ds

def maps {β γ : Type} : List β → (β → γ) → List γ
  | [], _ => []
  | d :: ds, f => f d :: maps ds f

def invs {β : Type} : List β → (β → Prop) → Prop
  | [], _ => True
  | d :: ds, φ => φ d ∧ invs ds φ

-- the first k elements of a sequence
def «prefix» {α : Type} (k : Int) (xs : List α) : List α :=
  xs.take k.toNat

-- whether x occurs in a sequence, and the index of its last occurrence (unspecified otherwise)
def occurs {α : Type} (x : α) (xs : List α) : Prop :=
  x ∈ xs

def indexof {α : Type} (x : α) (xs : List α) : Int :=
  (xs.length : Int) - 1 - (xs.reverse.findIdx (fun y => decide (y = x)) : Int)

-- whether a sequence has no duplicates
def distincts {α : Type} (xs : List α) : Prop :=
  xs.Nodup

-- consts(n, v) is the trace v, ..., v of n steps (the trace v if n <= 0)
def consts {α : Type} (n : Int) (v : α) : Trace α :=
  if n ≤ 0 then .stop v else .step (consts (n - 1) v) v
termination_by n.toNat
decreasing_by omega

-- the sum, parity (the number of even minus the number of odd elements), and number of occurrences of a value in
-- a sequence
def sum (values : List Int) : Int :=
  values.foldl (· + ·) 0

def parity (values : List Int) : Int :=
  values.foldl (fun p v => if v % 2 = 0 then p + 1 else p - 1) 0

def count {α : Type} (e : α) (vs : List α) : Int :=
  vs.foldl (fun c v => if v = e then c + 1 else c) 0

-- auxiliary predicates, which teq.dfy declares only, defined by the iteration constraints that they abstract:
-- the first n values of xs and ys agree, the first n values of ts exceed their positions
def agree_prefix (n : Int) (xs ys : List Int) : Prop :=
  ∀ k, 0 ≤ k → k < n → earlier k xs = earlier k ys

def above_iterations (n : Int) (ts : List Int) : Prop :=
  ∀ k, 0 ≤ k → k < n → k < earlier k ts

-- powers, which the simplifier does not unfold
def pow (c n : Int) : Int :=
  c ^ n.toNat

-- a variable that is increased by c in each iteration is a counter (example 2.3 of the paper)
theorem counter_def (i : Int) (c : Int) (n : Int) :
  trace i (butlast (counter 0 1 n)) (fun x k => x + c) = counter i c n :=
  by sorry

-- a variable that keeps its value in each iteration
theorem consts_def {α : Type} [Inhabited α] (x : α) (i : Int) (c : Int) (n : Int) :
  trace x (butlast (counter i c n)) (fun y v => y) = consts n x :=
  by sorry

-- the trace of the successive stores of the values at the keys into a
def stores {α β : Type} (a : α → β) (keys : List α)
                        (values : List β) : Trace (α → β) :=
  trace
    a
    (List.zip keys values)
    (fun b ⟨k, v⟩ => fun j => if j = k then v else b j)

-- each key is visited once only if they are distinct, hence b[k] is still the initial value a[k],
-- in any context f of the read, which may depend on the other dependencies, but not on the accumulator otherwise
theorem trace_read_initial {α β : Type} [Inhabited α] [Inhabited β] (a : α → β) (keys : List α)
                                                                    (fs : List (β → β)) :
  distincts keys
    → trace
      a
      (List.zip keys fs)
      (fun b ⟨k, f⟩ => fun j => if j = k then f (b k) else b j)
      = trace
        a
        (List.zip keys fs)
        (fun b ⟨k, f⟩ => fun j => if j = k then f (a k) else b j) :=
  by sorry

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
def counts {α : Type} (x : Int) (e : α)
                      (vs : List α) : Trace Int :=
  trace x vs (fun y v => if v = e then y + 1 else y)

-- on booleans, the guards are the values themselves; the occurrences of false come first,
-- since the guard b of the other lemma also matches !b, which counts the occurrences of true among the negations
theorem counts_false_def (x : Int) (bs : List Prop) :
  trace x bs (fun y b => if ¬b then y + 1 else y) = counts x False bs :=
  by sorry

theorem counts_true_def (x : Int) (bs : List Prop) :
  trace x bs (fun y b => if b then y + 1 else y) = counts x True bs :=
  by sorry

-- two cases whose results agree under the guard of the second one, x == c, which the simplifier has substituted
-- into it, are one; the second result is a variable d, since F(c) would be compared literally
-- (from copysome1-1, copysome1-2)
theorem trace_merge_cases_ne (x0 : Int) (n : Int) (c : Int) (d : Int)
                             (F : Int → Int) :
  d = F c
    → trace x0 (butlast (counter 0 1 n)) (fun x k => if x ≠ c then F x else d)
      = trace x0 (butlast (counter 0 1 n)) (fun x k => F x) :=
  by sorry

-- the same with the guards in the other order
-- (from brs1, brs1f, ifcomp, ms1, ms1f)
theorem trace_merge_cases_eq (x0 : Int) (n : Int) (c : Int) (d : Int)
                             (F : Int → Int) :
  d = F c
    → trace x0 (butlast (counter 0 1 n)) (fun x k => if x = c then d else F x)
      = trace x0 (butlast (counter 0 1 n)) (fun x k => F x) :=
  by sorry

-- stores at the positions 0, ..., n - 1 of values read from the array itself outside of that range read the initial
-- array
-- (from standard_palindrome_ground)
theorem stores_def_read_unmodified (a0 : Int → Int) (n : Int)
                                   (hs : List Int) (F : Int → Int → Int) :
  invs (List.zip (butlast (counter 0 1 n)) hs) (fun ⟨k, h⟩ => n ≤ F k h)
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
  by sorry

-- maps

theorem maps_const {α : Type} [Inhabited α] (x : α) (i : Int) (c : Int) (n : Int) :
  maps (butlast (counter i c n)) (fun v => x) = butlast (consts n x) :=
  by sorry

theorem maps_earlier {α : Type} [Inhabited α] (n : Int) (xs : List α) :
  maps (butlast (counter 0 1 n)) (fun k => earlier k xs) = xs :=
  by sorry

theorem maps_counter_affine (a : Int) (b : Int) (i : Int) (c : Int)
                            (n : Int) :
  maps (butlast (counter i c n)) (fun v => a + b * v)
    = butlast (counter (a + b * i) (b * c) n) :=
  by sorry

-- the values of a at the keys
def selects {α β : Type} (a : α → β) (keys : List α) : List β :=
  maps keys (fun k => a k)

-- invs

theorem invs_const (b : Prop) (i : Int) (c : Int) (n : Int) :
  invs (butlast (counter i c n)) (fun v => b) ↔ n = 0 ∨ b :=
  by sorry

theorem invs_counter_lower (m : Int) (i : Int) (c : Int) (n : Int) :
  invs (butlast (counter i c n)) (fun k => m ≤ k)
    ↔ n = 0 ∨ m ≤ i ∧ m ≤ i + (n - 1) * c :=
  by sorry

theorem invs_counter_upper (m : Int) (i : Int) (c : Int) (n : Int) :
  invs (butlast (counter i c n)) (fun k => k < m)
    ↔ n = 0 ∨ i < m ∧ i + (n - 1) * c < m :=
  by sorry

-- a counter by 1 or -1 avoids m if m lies outside of its range, e.g. for loops i != N
theorem invs_counter_ne_up (m : Int) (i : Int) (n : Int) :
  invs (butlast (counter i 1 n)) (fun k => k ≠ m) ↔ m < i ∨ i + n ≤ m :=
  by sorry

theorem invs_counter_ne_down (m : Int) (i : Int) (n : Int) :
  invs (butlast (counter i (-1) n)) (fun k => k ≠ m) ↔ i < m ∨ m ≤ i - n :=
  by sorry

-- the same counter is increasing for 0 < c, hence an upper bound B holds at all its values before the current one
-- iff it holds at the last of them
-- (from Mono1_1-2)
theorem invs_two_phases (x0 : Int) (n : Int) (b : Int) (c : Int)
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
         ↔ n = 0
           ∨ (if n - 1 ≤ b - x0 then x0 + n - 1 else b + (n - 1 - (b - x0)) * c)
             < B) :=
  by sorry

-- a lower bound of the values x of a counter with an arbitrary step holds in all iterations iff it holds at both
-- ends, since the values are linear; for a counter as the third of three dependencies, with the bound as 0 < x + c,
-- since b < x does not match k < x + n (see TODO.md)
-- (from benchmark04_conjunctive, benchmark09_conjunctive)
theorem invs_counter_positive_last (i : Int) (d : Int) (n : Int) (c : Int)
                                   (hs : List Int) (gs : List Int) :
  invs
    (List.zip hs (List.zip gs (butlast (counter i d n))))
    (fun ⟨h, g, x⟩ => 0 < x + c)
    ↔ n = 0 ∨ 0 < i + c ∧ 0 < i + (n - 1) * d + c :=
  by sorry

-- the same for a counter as the second of three dependencies
-- (from benchmark09_conjunctive)
theorem invs_counter_positive_middle (i : Int) (d : Int) (n : Int)
                                     (c : Int) (hs : List Int)
                                     (gs : List Int) :
  invs
    (List.zip hs (List.zip (butlast (counter i d n)) gs))
    (fun ⟨h, x, g⟩ => 0 < x + c)
    ↔ n = 0 ∨ 0 < i + c ∧ 0 < i + (n - 1) * d + c :=
  by sorry

-- an iteration constraint that is a negated disjunction, as the test of a break, is two of them
-- (from benchmark09_conjunctive)
theorem invs_not_or (hs : List Int) (gs : List Int) (fs : List Int)
                    (P : Int → Int → Int → Prop)
                    (Q : Int → Int → Int → Prop) :
  invs (List.zip hs (List.zip gs fs)) (fun ⟨h, g, f⟩ => ¬(P h g f ∨ Q h g f))
    ↔ invs (List.zip hs (List.zip gs fs)) (fun ⟨h, g, f⟩ => ¬P h g f)
      ∧ invs (List.zip hs (List.zip gs fs)) (fun ⟨h, g, f⟩ => ¬Q h g f) :=
  by sorry

-- two sequences that are equal at the iterations 0, ..., n - 1 agree there
-- (from standard_compare_ground)
theorem agree_prefix_def (n : Int) (xs : List Int) (ys : List Int)
                         (hs : List Int) :
  invs
    (List.zip (butlast (counter 0 1 n)) hs)
    (fun ⟨k, h⟩ => earlier k xs = earlier k ys)
    ↔ agree_prefix n xs ys :=
  by sorry

-- a search: the elements before the exit n differ from e, i.e., e does not occur in the prefix of length n
-- (from standard_find_ground-1)
theorem not_occurs_prefix_def (n : Int) (e : Int) (xs : List Int)
                              (hs : List Int) :
  invs (List.zip (butlast (counter 0 1 n)) hs) (fun ⟨k, h⟩ => earlier k xs ≠ e)
    ↔ ¬occurs e («prefix» n xs) :=
  by sorry

-- the values of the iterations exceed the iterations
-- (from simple_array_index_value_2)
theorem above_iterations_def (n : Int) (ts : List Int) (hs : List Int) :
  invs
    (List.zip (butlast (counter 0 1 n)) (List.zip hs ts))
    (fun ⟨k, h, t⟩ => k < t)
    ↔ above_iterations n ts :=
  by sorry

-- current

theorem current_counter (i : Int) (c : Int) (n : Int) :
  current (counter i c n) = i + n * c :=
  by sorry

theorem current_trace_constant {α : Type} [Inhabited α] (x : α) (y : α) (i : Int)
                                                        (c : Int) (n : Int) :
  current (trace x (butlast (counter i c n)) (fun z v => y))
    = (if n = 0 then x else y) :=
  by sorry

theorem current_consts {α : Type} [Inhabited α] (n : Int) (x : α) :
  current (consts n x) = x :=
  by sorry

theorem current_trace_add_at {α : Type} [Inhabited α] (a : α → Int) (k : α)
                                                      (values : List Int) :
  current (trace a values (fun b v => fun j => if j = k then b k + v else b j))
    = (fun j => if j = k then a k + sum values else a j) :=
  by sorry

theorem current_sums (x : Int) (values : List Int) :
  current (sums x values) = x + sum values :=
  by sorry

theorem current_parities (x : Int) (values : List Int) :
  current (parities x values) = x + parity values :=
  by sorry

theorem current_maxs_counter (x : Int) (i : Int) (c : Int) (n : Int) :
  current (maxs x (butlast (counter i c n)))
    = (if n = 0 then x else max x (max i (i + (n - 1) * c))) :=
  by sorry

theorem current_maxs_consts (x : Int) (y : Int) (n : Int) :
  current (maxs x (butlast (consts n y))) = (if n = 0 then x else max x y) :=
  by sorry

theorem current_mins_counter (x : Int) (i : Int) (c : Int) (n : Int) :
  current (mins x (butlast (counter i c n)))
    = (if n = 0 then x else min x (min i (i + (n - 1) * c))) :=
  by sorry

theorem current_mins_consts (x : Int) (y : Int) (n : Int) :
  current (mins x (butlast (consts n y))) = (if n = 0 then x else min x y) :=
  by sorry

theorem current_counts {α : Type} [Inhabited α] (x : Int) (e : α) (vs : List α) :
  current (counts x e vs) = x + count e vs :=
  by sorry

-- a counter in two phases: by 1 up to the bound b, from an initial value up to b, then by c >= 0, which keeps it
-- at least b
-- (from Mono1_1-2, phases_1-1, phases_1-2)
theorem current_trace_two_phases (x0 : Int) (n : Int) (b : Int)
                                 (c : Int) :
  x0 ≤ b ∧ 0 ≤ c
    → current
      (trace
         x0
         (butlast (counter 0 1 n))
         (fun x k => if x < b then x + 1 else x + c))
      = (if n ≤ b - x0 then x0 + n else b + (n - (b - x0)) * c) :=
  by sorry

-- a follower: y increases by 1 whenever it does not exceed the value x of a counter with step 1, hence y is the
-- larger of its initial value and the final value of x, given that it starts at least at x
-- (from benchmark05_conjunctive)
theorem current_trace_catch_up (y0 : Int) (x0 : Int) (n : Int) :
  x0 ≤ y0
    → current
      (trace
         y0
         (List.zip (butlast (counter 0 1 n)) (butlast (counter x0 1 n)))
         (fun y ⟨k, x⟩ => if y ≤ x then y + 1 else y))
      = (if x0 + n ≤ y0 then y0 else x0 + n) :=
  by sorry

-- a flag, initially x0, that is set to c whenever D holds, is x0 at the end iff D never held, otherwise c
-- (from standard_compare_ground)
theorem current_trace_flag (x0 : Int) (c : Int) (n : Int) (hs : List Int)
                           (D : Int → Int → Prop) :
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
  by sorry

-- a value multiplied by c in each iteration, a geometric sequence
-- (from underapprox_1-1, underapprox_1-2)
theorem current_trace_geometric (x0 : Int) (c : Int) (n : Int) :
  current (trace x0 (butlast (counter 0 1 n)) (fun x k => c * x)) = x0 * pow c n :=
  by sorry

-- a value whose two increments are multiples of m keeps its remainder modulo m, a modular invariant
-- (from loopv1)
theorem current_trace_mod (x0 : Int) (n : Int) (a : Int) (b : Int)
                          (m : Int) (hs : List Int) (C : Int → Prop) :
  0 < m ∧ a % m = 0 ∧ b % m = 0
    → current
      (trace
         x0
         (List.zip (butlast (counter 0 1 n)) hs)
         (fun x ⟨k, h⟩ => if C h then x + a else x + b))
      % m
      = x0 % m :=
  by sorry

-- a sum that is set to c in the first iteration and adds G(i) in the others is c plus the sum of G over 1, ..., n - 1,
-- stated as G(k + 1) over 0, ..., n - 2, since the context of a map knows the range of counter(0, 1, n) only
-- (from brs1, brs1f, ms1, ms1f)
theorem current_trace_reset_add (x0 : Int) (n : Int) (c : Int)
                                (G : Int → Int) :
  current
    (trace
       x0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
       (fun x ⟨k, i⟩ => if i = 0 then c else G i + x))
    = (if n = 0 then
         x0
       else
         c + sum (maps (butlast (counter 0 1 (n - 1))) (fun k => G (k + 1)))) :=
  by sorry

-- earlier

theorem earlier_counter (k : Int) (i : Int) (c : Int) (n : Int) :
  earlier k (butlast (counter i c n)) = i + k * c :=
  by sorry

theorem earlier_indexof {α : Type} [Inhabited α] (x : α) (xs : List α) :
  occurs x xs → earlier (indexof x xs) xs = x :=
  by sorry

theorem earlier_consts {α : Type} [Inhabited α] (k : Int) (n : Int) (x : α) :
  earlier k (butlast (consts n x)) = x :=
  by sorry

theorem earlier_selects {α β : Type} [Inhabited α] [Inhabited β] (j : Int) (a : α → β)
                                                                 (keys : List α) :
  earlier j (selects a keys) = a (earlier j keys) :=
  by sorry

theorem earlier_sums (j : Int) (x : Int) (values : List Int) :
  earlier j (butlast (sums x values)) = x + sum («prefix» j values) :=
  by sorry

theorem earlier_counts {α : Type} [Inhabited α] (j : Int) (x : Int) (e : α)
                                                (vs : List α) :
  earlier j (butlast (counts x e vs)) = x + count e («prefix» j vs) :=
  by sorry

theorem earlier_prefix {α : Type} [Inhabited α] (j : Int) (k : Int) (xs : List α) :
  earlier j («prefix» k xs) = earlier j xs :=
  by sorry

-- agreeing sequences are equal at each position in the range; the atom is the left-hand side
-- (from standard_compare_ground)
theorem earlier_agree_prefix (n : Int) (j : Int) (xs : List Int)
                             (ys : List Int) :
  agree_prefix n xs ys ∧ 0 ≤ j ∧ j < n → (earlier j xs = earlier j ys ↔ True) :=
  by sorry

-- which is instantiated at the positions j in that range
-- (from standard_find_ground-1)
theorem earlier_not_occurs_prefix (n : Int) (j : Int) (e : Int)
                                  (xs : List Int) :
  ¬occurs e («prefix» n xs) ∧ 0 ≤ j ∧ j < n → (earlier j xs = e ↔ False) :=
  by sorry

-- prefix

theorem prefix_counter (k : Int) (i : Int) (c : Int) (n : Int) :
  «prefix» k (butlast (counter i c n)) = butlast (counter i c k) :=
  by sorry

theorem prefix_consts {α : Type} [Inhabited α] (k : Int) (n : Int) (x : α) :
  «prefix» k (butlast (consts n x)) = butlast (consts k x) :=
  by sorry

theorem prefix_selects {α β : Type} [Inhabited α] [Inhabited β] (k : Int) (a : α → β)
                                                                (keys : List α) :
  «prefix» k (selects a keys) = selects a («prefix» k keys) :=
  by sorry

theorem prefix_stores {α β : Type} [Inhabited α] [Inhabited β] (k : Int) (a : α → β) (keys : List α)
                                                               (values : List β) :
  «prefix» k (butlast (stores a keys values))
    = butlast (stores a («prefix» k keys) («prefix» k values)) :=
  by sorry

theorem prefix_sums (k : Int) (x : Int) (values : List Int) :
  «prefix» k (butlast (sums x values)) = butlast (sums x («prefix» k values)) :=
  by sorry

theorem prefix_maxs (k : Int) (x : Int) (values : List Int) :
  «prefix» k (butlast (maxs x values)) = butlast (maxs x («prefix» k values)) :=
  by sorry

theorem prefix_mins (k : Int) (x : Int) (values : List Int) :
  «prefix» k (butlast (mins x values)) = butlast (mins x («prefix» k values)) :=
  by sorry

theorem prefix_counts {α : Type} [Inhabited α] (k : Int) (x : Int) (e : α)
                                               (vs : List α) :
  «prefix» k (butlast (counts x e vs)) = butlast (counts x e («prefix» k vs)) :=
  by sorry

theorem prefix_zero {α : Type} [Inhabited α] (xs : List α) : «prefix» 0 xs = [] :=
  by sorry

theorem prefix_prefix {α : Type} [Inhabited α] (j : Int) (k : Int) (xs : List α) :
  «prefix» j («prefix» k xs) = «prefix» j xs :=
  by sorry

-- occurs

-- a value read at one of the keys occurs among the values read at them
theorem occurs_selects {α β : Type} [Inhabited α] [Inhabited β] (k : α) (a : α → β) (keys : List α) :
  occurs k keys → occurs (a k) (selects a keys) :=
  by sorry

-- a value at an index occurs in the sequence, e.g. a stored value, which current(stores(a, keys, values))[k] reads
-- as earlier(indexof(k, keys), values) if k occurs among the keys; the indices of earlier are valid by construction
theorem occurs_earlier {α : Type} [Inhabited α] (j : Int) (xs : List α) :
  occurs (earlier j xs) xs :=
  by sorry

theorem occurs_counter_up (j : Int) (i : Int) (n : Int) :
  occurs j (butlast (counter i 1 n)) ↔ i ≤ j ∧ j < i + n :=
  by sorry

theorem occurs_counter_down (j : Int) (i : Int) (n : Int) :
  occurs j (butlast (counter i (-1) n)) ↔ i - n < j ∧ j ≤ i :=
  by sorry

theorem occurs_consts {α : Type} [Inhabited α] (x : α) (n : Int) (y : α) :
  occurs x (butlast (consts n y)) ↔ n ≠ 0 ∧ x = y :=
  by sorry

theorem occurs_prefix {α : Type} [Inhabited α] (x : α) (k : Int) (xs : List α) :
  occurs x («prefix» k xs) → occurs x xs :=
  by sorry

-- j occurs among the values of a counter with a positive step d iff it is in the range and a multiple of d from the
-- initial value (teq.dfy has this for the step 1)
-- (from array_monotonic)
theorem occurs_counter_step (i : Int) (d : Int) (n : Int) (j : Int) :
  0 < d
    → (occurs j (butlast (counter i d n))
         ↔ i ≤ j ∧ j < i + n * d ∧ (j - i) % d = 0) :=
  by sorry

-- indexof

theorem indexof_counter_up (j : Int) (i : Int) (n : Int) :
  i ≤ j ∧ j < i + n → indexof j (butlast (counter i 1 n)) = j - i :=
  by sorry

theorem indexof_counter_down (j : Int) (i : Int) (n : Int) :
  i - n < j ∧ j ≤ i → indexof j (butlast (counter i (-1) n)) = i - j :=
  by sorry

-- distincts

theorem distincts_counter (i : Int) (c : Int) (n : Int) :
  c ≠ 0 → distincts (butlast (counter i c n)) :=
  by sorry

theorem distincts_prefix {α : Type} [Inhabited α] (k : Int) (xs : List α) :
  distincts xs → distincts («prefix» k xs) :=
  by sorry

-- length

-- the length of the iterations of a counter
-- (from sumt2)
theorem length_counter (i : Int) (c : Int) (n : Int) :
  0 ≤ n → ((butlast (counter i c n)).length : Int) = n :=
  by sorry

-- selects

theorem selects_stores {α β : Type} [Inhabited α] [Inhabited β] (a : α → β) (keys : List α)
                                                                (values : List β) :
  distincts keys → selects (current (stores a keys values)) keys = values :=
  by sorry

theorem selects_shifts (a : Int → Int) (n : Int) (i : Int) (d : Int) :
  0 ≤ d
    → selects
      (current (shifts a (butlast (counter i 1 n)) d))
      (butlast (counter i 1 n))
      = selects a (butlast (counter (i + d) 1 n)) :=
  by sorry

-- the elements of stores at the positions of a counter, read at the positions of the same counter, are the stored
-- values; both counters are patterns, since they are different trace variables in programs
-- (from conda, condaf, ss1, ss1f)
theorem selects_stores_counter (a : Int → Int) (i : Int) (c : Int)
                               (n : Int) (vs : List Int) :
  c ≠ 0
    → selects
      (current (stores a (butlast (counter i c n)) vs))
      (butlast (counter i c n))
      = vs :=
  by sorry

-- array selects

theorem current_stores {α β : Type} [Inhabited α] [Inhabited β] (k : α) (a : α → β) (keys : List α)
                                                                (values : List β) :
  current (stores a keys values) k
    = (if occurs k keys then earlier (indexof k keys) values else a k) :=
  by sorry

-- an earlier state reads the value stored last at k among the keys stored so far, the initial value otherwise
-- (indexof is the *last* occurrence, hence indexof(k, prefix(j, keys)) <= indexof(k, keys) but not equal)
theorem earlier_stores {α β : Type} [Inhabited α] [Inhabited β] (k : α) (j : Int) (a : α → β)
                                                                (keys : List α) (values : List β) :
  earlier j (butlast (stores a keys values)) k
    = (if occurs k («prefix» j keys) then
         earlier (indexof k («prefix» j keys)) values
       else
         a k) :=
  by sorry

theorem current_shifts (a : Int → Int) (n : Int) (i : Int) (d : Int)
                       (k : Int) :
  0 ≤ d
    → current (shifts a (butlast (counter i 1 n)) d) k
      = (if i ≤ k ∧ k < i + n then a (k + d) else a k) :=
  by sorry

-- stores at the positions of a counter, guarded by C, keep the other positions; a read at j
-- (from copysome1-1, copysome1-2)
theorem current_trace_conditional_store (a0 : Int → Int) (n : Int)
                                        (j : Int) (C : Int → Prop)
                                        (V : Int → Int) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
       (fun a ⟨k, i⟩ => if C i then fun j => if j = i then V i else a j else a))
    j
    = (if 0 ≤ j ∧ j < n ∧ C j then V j else a0 j) :=
  by sorry

-- the same, with the guard and the value on the values of three further dependencies at the iteration of j
-- (from array_mul_init)
theorem current_trace_conditional_store_deps (a0 : Int → Int) (n : Int)
                                             (j : Int) (hs : List Int)
                                             (cs : List Int)
                                             (vs : List Int)
                                             (C : Int → Int → Int → Prop)
                                             (V : Int → Int → Int → Int) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) (List.zip hs (List.zip cs vs)))
       (fun a ⟨k, h, c, v⟩ =>
          if C h c v then fun j => if j = k then V h c v else a j else a))
    j
    = (if 0 ≤ j ∧ j < n ∧ C (earlier j hs) (earlier j cs) (earlier j vs) then
         V (earlier j hs) (earlier j cs) (earlier j vs)
       else
         a0 j) :=
  by sorry

-- the same, at distinct positions ps, which are kept as matched, read by occurs and indexof
-- (from array_monotonic)
theorem current_trace_conditional_store_distinct (a0 : Int → Int)
                                                 (n : Int) (j : Int)
                                                 (ps : List Int)
                                                 (cs : List Int)
                                                 (C : Int → Int → Prop)
                                                 (V : Int → Int → Int) :
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
  by sorry

-- a clamp of each element to b, where the guard reads the initial element, since each position is written in its own
-- iteration only; a generic guard C(a[k], k) is no pattern, and C(a, k) would read other positions
-- (from condn, condnf)
theorem current_trace_cap (a0 : Int → Int) (n : Int) (j : Int) (b : Int)
                          (hs : List Int) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) hs)
       (fun a ⟨k, h⟩ =>
          if a k < b then a else fun j => if j = k then b else a j))
    j
    = (if 0 ≤ j ∧ j < n ∧ b ≤ a0 j then b else a0 j) :=
  by sorry

-- an array filled by a recurrence at the positions 1, ..., n, each element from its predecessor plus G of the position
-- of the predecessor, is the initial element plus the sum of G over the positions before
-- (from eqn1, eqn1f, nsqm, nsqmf, pcomp, pcompf, sqm)
theorem current_trace_prefix_sums (b0 : Int → Int) (n : Int) (j : Int)
                                  (G : Int → Int) :
  current
    (trace
       b0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 1 1 n)))
       (fun b ⟨k, i⟩ => fun j => if j = i then G k + b k else b j))
    j
    = (if 0 ≤ j ∧ j ≤ n then
         b0 0 + sum (maps (butlast (counter 0 1 j)) (fun k => G k))
       else
         b0 j) :=
  by sorry

-- the same with two added terms, since a higher-order summand matches a single summand only (see TODO.md)
-- (from nsqm, nsqmf, pcomp, pcompf, sqm)
theorem current_trace_prefix_sums_add (b0 : Int → Int) (n : Int) (j : Int)
                                      (G : Int → Int) (H : Int → Int) :
  current
    (trace
       b0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 1 1 n)))
       (fun b ⟨k, i⟩ => fun j => if j = i then b k + G k + H k else b j))
    j
    = (if 0 ≤ j ∧ j ≤ n then
         b0 0 + sum (maps (butlast (counter 0 1 j)) (fun k => G k + H k))
       else
         b0 j) :=
  by sorry

-- the special case of a constant added term
-- (from standard_seq_init_ground)
theorem current_trace_prefix_const (a0 : Int → Int) (n : Int) (c : Int)
                                   (j : Int) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 1 1 n)))
       (fun a ⟨k, i⟩ => fun j => if j = i then a k + c else a j))
    j
    = (if 1 ≤ j ∧ j ≤ n then a0 0 + j * c else a0 j) :=
  by sorry

-- sum, which is linear, and the linear transformations are moved to the outside

theorem sum_empty : sum [] = 0 :=
  by sorry

theorem sum_consts (n : Int) (x : Int) :
  sum (butlast (consts n x)) = x * n :=
  by sorry

theorem sum_neg (values : List Int) :
  sum (maps values (fun v => -v)) = -sum values :=
  by sorry

theorem sum_scale (values : List Int) (a : Int) :
  sum (maps values (fun v => a * v)) = a * sum values :=
  by sorry

theorem sum_add (xs : List Int) (ys : List Int) :
  sum (maps (List.zip xs ys) (fun ⟨v, w⟩ => v + w)) = sum xs + sum ys :=
  by sorry

-- the arithmetic series, which is exact, since n * (n - 1) is even
theorem sum_counter (i : Int) (c : Int) (n : Int) :
  sum (butlast (counter i c n)) = (2 * i + (n - 1) * c) * n / 2 :=
  by sorry

theorem sum_selects_update {α : Type} [Inhabited α] (a : α → Int) (k : α) (v : Int)
                                                    (keys : List α) :
  distincts keys
    → sum (selects (fun j => if j = k then v else a j) keys)
      = (if occurs k keys then
           sum (selects a keys) + v - a k
         else
           sum (selects a keys)) :=
  by sorry

-- parity

theorem parity_selects_update {α : Type} [Inhabited α] (a : α → Int) (k : α) (v : Int)
                                                       (keys : List α) :
  distincts keys
    → parity (selects (fun j => if j = k then v else a j) keys)
      = (if occurs k keys then
           parity (selects a keys) + (if v % 2 = 0 then 1 else -1)
             - (if a k % 2 = 0 then 1 else -1)
         else
           parity (selects a keys)) :=
  by sorry

-- count

theorem count_consts {α : Type} [Inhabited α] (n : Int) (e : α) (v : α) :
  count e (butlast (consts n v)) = (if v = e then n else 0) :=
  by sorry

-- an update of a visited key replaces its contribution, as for sum and parity
theorem count_selects_update {α β : Type} [Inhabited α] [Inhabited β] (a : α → β) (k : α) (w : β)
                                                                      (e : β) (keys : List α) :
  distincts keys
    → count e (selects (fun j => if j = k then w else a j) keys)
      = (if occurs k keys then
           count e (selects a keys) + (if w = e then 1 else 0)
             - (if a k = e then 1 else 0)
         else
           count e (selects a keys)) :=
  by sorry

-- the iterations of a counter by 1 before m and from m on, e.g. for loops with if (i < m) in the body
theorem count_true_below (m : Int) (i : Int) (n : Int) :
  i ≤ m ∧ m ≤ i + n
    → count True (maps (butlast (counter i 1 n)) (fun k => k < m)) = m - i :=
  by sorry

theorem count_false_below (m : Int) (i : Int) (n : Int) :
  i ≤ m ∧ m ≤ i + n
    → count False (maps (butlast (counter i 1 n)) (fun k => k < m)) = i + n - m :=
  by sorry

theorem count_true_above (m : Int) (i : Int) (n : Int) :
  i ≤ m ∧ m ≤ i + n
    → count True (maps (butlast (counter i 1 n)) (fun k => m ≤ k)) = i + n - m :=
  by sorry

theorem count_false_above (m : Int) (i : Int) (n : Int) :
  i ≤ m ∧ m ≤ i + n
    → count False (maps (butlast (counter i 1 n)) (fun k => m ≤ k)) = m - i :=
  by sorry

theorem count_nonnegative {α : Type} [Inhabited α] (e : α) (vs : List α) :
  0 ≤ count e vs :=
  by sorry

-- the numbers 0, ..., n - 1 with the remainder r modulo m number (n + m - 1 - r) / m
-- (from half, sumt2)
theorem count_remainder (n : Int) (m : Int) (r : Int) (hs : List Int) :
  0 ≤ n ∧ 0 < m ∧ 0 ≤ r ∧ r < m
    → count
      r
      (maps (List.zip (butlast (counter 0 1 n)) hs) (fun ⟨k, h⟩ => k % m))
      = (n + m - 1 - r) / m :=
  by sorry

-- among the truth values of a map, those that are false are the others than those that are true; the dependencies
-- are kept as matched, such that the counts are syntactically equal to those of the program
-- (from sumt2)
theorem count_false_true (ks : List Int) (hs : List Int)
                         (P : Int → Int → Prop) :
  count False (maps (List.zip ks hs) (fun ⟨k, h⟩ => P k h))
    = (ks.length : Int)
      - count True (maps (List.zip ks hs) (fun ⟨k, h⟩ => P k h)) :=
  by sorry

-- the iterations where a value is r are counted by the occurrences of r among the values
-- (from sumt2)
theorem count_true_eq (ks : List Int) (r : Int) (hs : List Int)
                      (F : Int → Int → Int) :
  count True (maps (List.zip ks hs) (fun ⟨k, h⟩ => F k h = r))
    = count r (maps (List.zip ks hs) (fun ⟨k, h⟩ => F k h)) :=
  by sorry

-- bounds

-- the initial value is a bound of the prefix maxima and minima, which are attained by some value otherwise
theorem current_maxs_initial (x : Int) (values : List Int) :
  x ≤ current (maxs x values) :=
  by sorry

theorem current_maxs_earlier (k : Int) (x : Int) (values : List Int) :
  earlier k values ≤ current (maxs x values) :=
  by sorry

theorem current_mins_initial (x : Int) (values : List Int) :
  current (mins x values) ≤ x :=
  by sorry

theorem current_mins_earlier (k : Int) (x : Int) (values : List Int) :
  current (mins x values) ≤ earlier k values :=
  by sorry

-- a value that increases by a positive constant in each of its three cases exceeds its initial value after at
-- least one iteration
-- (from large_const)
theorem current_trace_increasing (x0 : Int) (n : Int) (a : Int) (b : Int)
                                 (c : Int) (hs : List Int)
                                 (C : Int → Prop) (D : Int → Prop)
                                 (E : Int → Prop) :
  0 < n ∧ 0 < a ∧ 0 < b ∧ 0 < c
    → x0
      < current
        (trace
           x0
           (List.zip (butlast (counter 0 1 n)) hs)
           (fun x ⟨k, h⟩ =>
              if C h then x + a else if D h then x + b else x + c)) :=
  by sorry

-- an interval that contains the initial value and that each of the three cases maps into itself contains the
-- current value, an inductive invariant; the left-hand side is the conjunction of both bounds, which binds both
-- (from benchmark51_polynomial)
theorem current_trace_bounded (x0 : Int) (n : Int) (lo : Int) (hi : Int)
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
              (fun x k => if C1 x then F1 x else if C2 x then F2 x else F3 x))
         ∧ current
           (trace
              x0
              (butlast (counter 0 1 n))
              (fun x k => if C1 x then F1 x else if C2 x then F2 x else F3 x))
           ≤ hi
         ↔ True) :=
  by sorry

-- which is instantiated at the positions j in the range
-- (from simple_array_index_value_2)
theorem earlier_above_iterations (n : Int) (j : Int) (ts : List Int) :
  above_iterations n ts ∧ 0 ≤ j ∧ j < n → (j < earlier j ts ↔ True) :=
  by sorry

-- arithmetic, in the normal form of the simplifier

-- even summands do not change the remainder modulo 2
-- (from array_monotonic, phases_1-1, phases_1-2)
theorem mod_add_even (x : Int) (n : Int) : (x + 2 * n) % 2 = x % 2 :=
  by sorry

-- a positive number divides itself
-- (from modn, modnf)
theorem mod_self (x : Int) : 0 < x → x % x = 0 :=
  by sorry

-- division of a multiple of m plus a remainder below m
-- (from half)
theorem div_quotient_remainder (m : Int) (k : Int) (r : Int) :
  0 < m ∧ 0 ≤ r ∧ r < m → (m * k + r) / m = k :=
  by sorry

-- twice a number is the product of consecutive numbers iff it is its half, as an equivalence of atoms, since an
-- equation of integers as a lemma rewrites its left-hand side as a term
-- (from gauss_sum)
theorem double_eq_half (n : Int) (s : Int) :
  2 * s = n + n * n ↔ s = (n + n * n) / 2 :=
  by sorry

-- the sum 0 + 1 + ... + (n - 1) plus 1 is at least n
-- (from afnp2014)
theorem triangle_bound (n : Int) : n ≤ (-n + n * n) / 2 + 1 :=
  by sorry

-- division by 2 of polynomials with even coefficients, since a generic (2 * a + 2 * b) / 2 does not match literal
-- coefficients
-- (from eqn1, eqn1f)
theorem half_2x_2xx (x : Int) : (2 * x + 2 * x * x) / 2 = x + x * x :=
  by sorry

-- the same
-- (from nsqm, nsqmf, sqm)
theorem half_4x_2xx (x : Int) : (4 * x + 2 * x * x) / 2 = 2 * x + x * x :=
  by sorry

-- the same
-- (from pcomp, pcompf)
theorem half_6x_6xx (x : Int) :
  (6 * x + 6 * x * x) / 2 = 3 * x + 3 * x * x :=
  by sorry

-- the differences (k + 1)^3 - k^3 - 1 = 3 * k + 3 * k * k telescope to n^3 - n; teq.dfy splits such a sum by linearity
-- first, hence the sum of 3 * k * k as the rest, such that the division atoms cancel
-- (from pcomp, pcompf)
theorem sum_squares (n : Int) :
  0 ≤ n
    → sum (maps (butlast (counter 0 1 n)) (fun k => 3 * k * k))
      = n * n * n - n - 3 * ((-n + n * n) / 2) :=
  by sorry

-- a power of 2 is not divisible by 3
-- (from underapprox_1-1, underapprox_1-2)
theorem pow_two_mod_three (n : Int) : 0 ≤ n → (pow 2 n % 3 = 0 ↔ False) :=
  by sorry

-- a nonnegative factor cancels in a strict comparison; does not match a literal coefficient (see TODO.md)
-- (from count_by_k)
theorem mul_lt_cancel (k : Int) (a : Int) (b : Int) :
  0 ≤ k → (k * a < k * b ↔ 0 < k ∧ a < b) :=
  by sorry

-- counterexamples: lemmas that hold only under further assumptions, which the contexts of the goals of -teq
-- provide, e.g. a nonnegative number of iterations, an index within the trace, or dependencies of equal length

-- invs_const without n ≥ 0: no iterations, but n ≠ 0
example : ¬ (invs (butlast (counter 0 1 (-1))) (fun _ => False) ↔ (-1 : Int) = 0 ∨ False) :=
  by simp [invs, butlast, counter]

-- current_counter without n ≥ 0: the trace of -1 steps is that of 0 steps
example : ¬ (current (counter 0 1 (-1)) = 0 + (-1) * 1) :=
  by simp [current, counter]

-- earlier_consts outside the trace
example : ¬ (earlier 5 (butlast (consts 0 (1 : Int))) = 1) :=
  by simp [earlier, butlast, consts]

-- prefix_prefix for j > k
example : ¬ («prefix» 2 («prefix» 1 [(1 : Int), 2]) = «prefix» 2 [1, 2]) :=
  by simp [«prefix»]

-- occurs_earlier for the empty sequence
example : ¬ (occurs (earlier 0 ([] : List Int)) []) :=
  by simp [occurs]

-- current_stores for dependencies of different lengths, which are zipped: the key 0 gets no value
example : ¬ (current (stores (fun _ => (1 : Int)) [0] []) 0
    = if occurs 0 [0] then earlier (indexof 0 [0]) ([] : List Int) else 1) :=
  by simp [stores, trace, traceFrom, current, occurs, earlier]

end TEQ
