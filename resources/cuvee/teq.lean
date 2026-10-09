/-
The semantics of the lemma database of -teq (teq.dfy) in Lean 4, without Mathlib: the datatype of traces, the
functions, which teq.dfy defines by recursion, and the lemmas are printed by
`./Cuvee.sh -print lean resources/cuvee/teq.dfy`, the lemmas as theorems to be proved, most of them still `sorry`;
the combinators are defined here.

Traces are the datatype of teq.dfy, a value followed by a trace (step) or a last value (stop), hence a trace is
never empty, and the trace combinator is a right fold over its dependency; the naturals and lists of teq.dfy are
those of Lean, arrays are functions. There is a single combinator of each kind, trace, maps, and invs, over a single dependency: several
dependencies are zipped into a list of tuples, which truncates them to the shortest one, whereas the dependencies of
the combinators of Cuvée have equal lengths, which teq.dfy does not state (see TODO.md); `case φ => e case ψ => f`
updates are conditionals (the guards are disjoint and complete).
Check with `lean resources/cuvee/teq.lean` (Lean 4.34).
-/
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace TEQ

-- the constructors of Nat and List, which are those of Lean ({:lean} in teq.dfy)
open Nat (zero succ)
open List (nil cons)

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

-- the first n values of ts exceed their positions
def above_iterations (n : Nat) (ts : List Int) : Prop :=
  match n with
  | .zero => True
  | .succ m => above_iterations m ts ∧ integer m < earlier m ts

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

theorem natural_integer (n : Nat) : natural (integer n) = n :=
  by sorry

theorem integer_natural (x : Int) : 0 ≤ x → integer (natural x) = x :=
  by sorry

theorem zero_integer (n : Nat) : n = zero ↔ integer n = 0 :=
  by sorry

-- traces

-- a variable that is increased by c in each iteration is a counter (example 2.3 of the paper)
theorem counter_def (i : Int) (c : Int) (n : Nat) :
  trace i (butlast (counter 0 1 n)) (fun x k => x + c) = counter i c n :=
  by sorry

-- a variable that keeps its value in each iteration
theorem consts_def {α : Type} [Inhabited α] (x : α) (i : Int) (c : Int) (n : Nat) :
  trace x (butlast (counter i c n)) (fun y v => y) = consts n x :=
  by sorry

-- the trace of the successive stores of the values at the keys into a
def stores {α β : Type} [Inhabited α] [Inhabited β] (a : α → β) (keys : List α)
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
def counts {α : Type} [Inhabited α] (x : Int) (e : α)
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
theorem trace_merge_cases_ne (x0 : Int) (n : Nat) (c : Int) (d : Int)
                             (F : Int → Int) :
  d = F c
    → trace x0 (butlast (counter 0 1 n)) (fun x k => if x ≠ c then F x else d)
      = trace x0 (butlast (counter 0 1 n)) (fun x k => F x) :=
  by sorry

-- the same with the guards in the other order
-- (from brs1, brs1f, ifcomp, ms1, ms1f)
theorem trace_merge_cases_eq (x0 : Int) (n : Nat) (c : Int) (d : Int)
                             (F : Int → Int) :
  d = F c
    → trace x0 (butlast (counter 0 1 n)) (fun x k => if x = c then d else F x)
      = trace x0 (butlast (counter 0 1 n)) (fun x k => F x) :=
  by sorry

-- stores at the positions 0, ..., n - 1 of values read from the array itself outside of that range read the initial
-- array
-- (from standard_palindrome_ground)
theorem stores_def_read_unmodified (a0 : Int → Int) (n : Nat)
                                   (hs : List Int) (F : Int → Int → Int) :
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
  by sorry

-- maps

theorem maps_const {α : Type} [Inhabited α] (x : α) (i : Int) (c : Int) (n : Nat) :
  maps (butlast (counter i c n)) (fun v => x) = butlast (consts n x) :=
  by sorry

theorem maps_earlier {α : Type} [Inhabited α] (n : Nat) (xs : List α) :
  maps (butlast (counter 0 1 n)) (fun k => earlier (natural k) xs) = xs :=
  by sorry

theorem maps_counter_affine (a : Int) (b : Int) (i : Int) (c : Int)
                            (n : Nat) :
  maps (butlast (counter i c n)) (fun v => a + b * v)
    = butlast (counter (a + b * i) (b * c) n) :=
  by sorry

-- the values of a at the keys
def selects {α β : Type} [Inhabited α] [Inhabited β] (a : α → β) (keys : List α) : List β :=
  maps keys (fun k => a k)

-- invs

theorem invs_const (b : Prop) (i : Int) (c : Int) (n : Nat) :
  invs (butlast (counter i c n)) (fun v => b) ↔ n = zero ∨ b :=
  by sorry

theorem invs_counter_lower (m : Int) (i : Int) (c : Int) (n : Nat) :
  invs (butlast (counter i c n)) (fun k => m ≤ k)
    ↔ n = zero ∨ m ≤ i ∧ m ≤ i + (integer n - 1) * c :=
  by sorry

theorem invs_counter_upper (m : Int) (i : Int) (c : Int) (n : Nat) :
  invs (butlast (counter i c n)) (fun k => k < m)
    ↔ n = zero ∨ i < m ∧ i + (integer n - 1) * c < m :=
  by sorry

-- a counter by 1 or -1 avoids m if m lies outside of its range, e.g. for loops i != N
theorem invs_counter_ne_up (m : Int) (i : Int) (n : Nat) :
  invs (butlast (counter i 1 n)) (fun k => k ≠ m) ↔ m < i ∨ i + integer n ≤ m :=
  by sorry

theorem invs_counter_ne_down (m : Int) (i : Int) (n : Nat) :
  invs (butlast (counter i (-1) n)) (fun k => k ≠ m) ↔ i < m ∨ m ≤ i - integer n :=
  by sorry

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
  by sorry

-- a lower bound of the values x of a counter with an arbitrary step holds in all iterations iff it holds at both
-- ends, since the values are linear; for a counter as the third of three dependencies, with the bound as 0 < x + c,
-- since b < x does not match k < x + n (see TODO.md)
-- (from benchmark04_conjunctive, benchmark09_conjunctive)
theorem invs_counter_positive_last (i : Int) (d : Int) (n : Nat) (c : Int)
                                   (hs : List Int) (gs : List Int) :
  invs
    (List.zip hs (List.zip gs (butlast (counter i d n))))
    (fun ⟨h, g, x⟩ => 0 < x + c)
    ↔ n = zero ∨ 0 < i + c ∧ 0 < i + (integer n - 1) * d + c :=
  by sorry

-- the same for a counter as the second of three dependencies
-- (from benchmark09_conjunctive)
theorem invs_counter_positive_middle (i : Int) (d : Int) (n : Nat)
                                     (c : Int) (hs : List Int)
                                     (gs : List Int) :
  invs
    (List.zip hs (List.zip (butlast (counter i d n)) gs))
    (fun ⟨h, x, g⟩ => 0 < x + c)
    ↔ n = zero ∨ 0 < i + c ∧ 0 < i + (integer n - 1) * d + c :=
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
theorem agree_prefix_def (n : Nat) (xs : List Int) (ys : List Int)
                         (hs : List Int) :
  invs
    (List.zip (butlast (counter 0 1 n)) hs)
    (fun ⟨k, h⟩ => earlier (natural k) xs = earlier (natural k) ys)
    ↔ agree_prefix n xs ys :=
  by sorry

-- a search: the elements before the exit n differ from e, i.e., e does not occur in the prefix of length n
-- (from standard_find_ground-1)
theorem not_occurs_prefix_def (n : Nat) (e : Int) (xs : List Int)
                              (hs : List Int) :
  invs
    (List.zip (butlast (counter 0 1 n)) hs)
    (fun ⟨k, h⟩ => earlier (natural k) xs ≠ e)
    ↔ ¬occurs e («prefix» n xs) :=
  by sorry

-- the values of the iterations exceed the iterations
-- (from simple_array_index_value_2)
theorem above_iterations_def (n : Nat) (ts : List Int) (hs : List Int) :
  invs
    (List.zip (butlast (counter 0 1 n)) (List.zip hs ts))
    (fun ⟨k, h, t⟩ => k < t)
    ↔ above_iterations n ts :=
  by sorry

-- current

theorem current_counter (i : Int) (c : Int) (n : Nat) :
  current (counter i c n) = i + integer n * c :=
  by sorry

theorem current_trace_constant {α : Type} [Inhabited α] (x : α) (y : α) (i : Int)
                                                        (c : Int) (n : Nat) :
  current (trace x (butlast (counter i c n)) (fun z v => y))
    = (if n = zero then x else y) :=
  by sorry

theorem current_consts {α : Type} [Inhabited α] (n : Nat) (x : α) :
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

theorem current_maxs_counter (x : Int) (i : Int) (c : Int) (n : Nat) :
  current (maxs x (butlast (counter i c n)))
    = (if n = zero then x else max x (max i (i + (integer n - 1) * c))) :=
  by sorry

theorem current_maxs_consts (x : Int) (y : Int) (n : Nat) :
  current (maxs x (butlast (consts n y))) = (if n = zero then x else max x y) :=
  by sorry

theorem current_mins_counter (x : Int) (i : Int) (c : Int) (n : Nat) :
  current (mins x (butlast (counter i c n)))
    = (if n = zero then x else min x (min i (i + (integer n - 1) * c))) :=
  by sorry

theorem current_mins_consts (x : Int) (y : Int) (n : Nat) :
  current (mins x (butlast (consts n y))) = (if n = zero then x else min x y) :=
  by sorry

theorem current_counts {α : Type} [Inhabited α] (x : Int) (e : α) (vs : List α) :
  current (counts x e vs) = x + count e vs :=
  by sorry

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
  by sorry

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
  by sorry

-- a flag, initially x0, that is set to c whenever D holds, is x0 at the end iff D never held, otherwise c
-- (from standard_compare_ground)
theorem current_trace_flag (x0 : Int) (c : Int) (n : Nat) (hs : List Int)
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
theorem current_trace_geometric (x0 : Int) (c : Int) (n : Nat) :
  current (trace x0 (butlast (counter 0 1 n)) (fun x k => c * x)) = x0 * pow c n :=
  by sorry

-- a value whose two increments are multiples of m keeps its remainder modulo m, a modular invariant
-- (from loopv1)
theorem current_trace_mod (x0 : Int) (n : Nat) (a : Int) (b : Int)
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
theorem current_trace_reset_add (x0 : Int) (n : Nat) (c : Int)
                                (G : Int → Int) :
  current
    (trace
       x0
       (List.zip (butlast (counter 0 1 n)) (butlast (counter 0 1 n)))
       (fun x ⟨k, i⟩ => if i = 0 then c else G i + x))
    = (match n with
       | .zero => x0
       | .succ m =>
         c + sum (maps (butlast (counter 0 1 m)) (fun k => G (k + 1)))) :=
  by sorry

-- earlier

theorem earlier_counter (k : Nat) (i : Int) (c : Int) (n : Nat) :
  earlier k (butlast (counter i c n)) = i + integer k * c :=
  by sorry

theorem earlier_indexof {α : Type} [Inhabited α] (x : α) (xs : List α) :
  occurs x xs → earlier (indexof x xs) xs = x :=
  by sorry

theorem earlier_consts {α : Type} [Inhabited α] (k : Nat) (n : Nat) (x : α) :
  earlier k (butlast (consts n x)) = x :=
  by sorry

theorem earlier_selects {α β : Type} [Inhabited α] [Inhabited β] (j : Nat) (a : α → β)
                                                                 (keys : List α) :
  earlier j (selects a keys) = a (earlier j keys) :=
  by sorry

theorem earlier_sums (j : Nat) (x : Int) (values : List Int) :
  earlier j (butlast (sums x values)) = x + sum («prefix» j values) :=
  by sorry

theorem earlier_counts {α : Type} [Inhabited α] (j : Nat) (x : Int) (e : α)
                                                (vs : List α) :
  earlier j (butlast (counts x e vs)) = x + count e («prefix» j vs) :=
  by sorry

theorem earlier_prefix {α : Type} [Inhabited α] (j : Nat) (k : Nat) (xs : List α) :
  earlier j («prefix» k xs) = earlier j xs :=
  by sorry

-- agreeing sequences are equal at each position in the range; the atom is the left-hand side
-- (from standard_compare_ground)
theorem earlier_agree_prefix (n : Nat) (j : Nat) (xs : List Int)
                             (ys : List Int) :
  agree_prefix n xs ys ∧ integer j < integer n
    → (earlier j xs = earlier j ys ↔ True) :=
  by sorry

-- which is instantiated at the positions j in that range
-- (from standard_find_ground-1)
theorem earlier_not_occurs_prefix (n : Nat) (j : Nat) (e : Int)
                                  (xs : List Int) :
  ¬occurs e («prefix» n xs) ∧ integer j < integer n → (earlier j xs = e ↔ False) :=
  by sorry

-- prefix

theorem prefix_counter (k : Nat) (i : Int) (c : Int) (n : Nat) :
  «prefix» k (butlast (counter i c n)) = butlast (counter i c k) :=
  by sorry

theorem prefix_consts {α : Type} [Inhabited α] (k : Nat) (n : Nat) (x : α) :
  «prefix» k (butlast (consts n x)) = butlast (consts k x) :=
  by sorry

theorem prefix_selects {α β : Type} [Inhabited α] [Inhabited β] (k : Nat) (a : α → β)
                                                                (keys : List α) :
  «prefix» k (selects a keys) = selects a («prefix» k keys) :=
  by sorry

theorem prefix_stores {α β : Type} [Inhabited α] [Inhabited β] (k : Nat) (a : α → β) (keys : List α)
                                                               (values : List β) :
  «prefix» k (butlast (stores a keys values))
    = butlast (stores a («prefix» k keys) («prefix» k values)) :=
  by sorry

theorem prefix_sums (k : Nat) (x : Int) (values : List Int) :
  «prefix» k (butlast (sums x values)) = butlast (sums x («prefix» k values)) :=
  by sorry

theorem prefix_maxs (k : Nat) (x : Int) (values : List Int) :
  «prefix» k (butlast (maxs x values)) = butlast (maxs x («prefix» k values)) :=
  by sorry

theorem prefix_mins (k : Nat) (x : Int) (values : List Int) :
  «prefix» k (butlast (mins x values)) = butlast (mins x («prefix» k values)) :=
  by sorry

theorem prefix_counts {α : Type} [Inhabited α] (k : Nat) (x : Int) (e : α)
                                               (vs : List α) :
  «prefix» k (butlast (counts x e vs)) = butlast (counts x e («prefix» k vs)) :=
  by sorry

theorem prefix_zero {α : Type} [Inhabited α] (xs : List α) : «prefix» zero xs = nil :=
  by sorry

theorem prefix_prefix {α : Type} [Inhabited α] (j : Nat) (k : Nat) (xs : List α) :
  «prefix» j («prefix» k xs) = «prefix» j xs :=
  by sorry

-- occurs

-- a value read at one of the keys occurs among the values read at them
theorem occurs_selects {α β : Type} [Inhabited α] [Inhabited β] (k : α) (a : α → β) (keys : List α) :
  occurs k keys → occurs (a k) (selects a keys) :=
  by sorry

-- a value at an index occurs in the sequence, e.g. a stored value, which current(stores(a, keys, values))[k] reads
-- as earlier(indexof(k, keys), values) if k occurs among the keys; the indices of earlier are valid by construction
theorem occurs_earlier {α : Type} [Inhabited α] (j : Nat) (xs : List α) :
  occurs (earlier j xs) xs :=
  by sorry

theorem occurs_counter_up (j : Int) (i : Int) (n : Nat) :
  occurs j (butlast (counter i 1 n)) ↔ i ≤ j ∧ j < i + integer n :=
  by sorry

theorem occurs_counter_down (j : Int) (i : Int) (n : Nat) :
  occurs j (butlast (counter i (-1) n)) ↔ i - integer n < j ∧ j ≤ i :=
  by sorry

theorem occurs_consts {α : Type} [Inhabited α] (x : α) (n : Nat) (y : α) :
  occurs x (butlast (consts n y)) ↔ n ≠ zero ∧ x = y :=
  by sorry

theorem occurs_prefix {α : Type} [Inhabited α] (x : α) (k : Nat) (xs : List α) :
  occurs x («prefix» k xs) → occurs x xs :=
  by sorry

-- j occurs among the values of a counter with a positive step d iff it is in the range and a multiple of d from the
-- initial value (teq.dfy has this for the step 1)
-- (from array_monotonic)
theorem occurs_counter_step (i : Int) (d : Int) (n : Nat) (j : Int) :
  0 < d
    → (occurs j (butlast (counter i d n))
         ↔ i ≤ j ∧ j < i + integer n * d ∧ (j - i) % d = 0) :=
  by sorry

-- indexof

theorem indexof_counter_up (j : Int) (i : Int) (n : Nat) :
  i ≤ j ∧ j < i + integer n
    → indexof j (butlast (counter i 1 n)) = natural (j - i) :=
  by sorry

theorem indexof_counter_down (j : Int) (i : Int) (n : Nat) :
  i - integer n < j ∧ j ≤ i
    → indexof j (butlast (counter i (-1) n)) = natural (i - j) :=
  by sorry

-- distincts

theorem distincts_counter (i : Int) (c : Int) (n : Nat) :
  c ≠ 0 → distincts (butlast (counter i c n)) :=
  by sorry

theorem distincts_prefix {α : Type} [Inhabited α] (k : Nat) (xs : List α) :
  distincts xs → distincts («prefix» k xs) :=
  by sorry

-- selects

theorem selects_stores {α β : Type} [Inhabited α] [Inhabited β] (a : α → β) (keys : List α)
                                                                (values : List β) :
  distincts keys → selects (current (stores a keys values)) keys = values :=
  by sorry

theorem selects_shifts (a : Int → Int) (n : Nat) (i : Int) (d : Int) :
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
                               (n : Nat) (vs : List Int) :
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
theorem earlier_stores {α β : Type} [Inhabited α] [Inhabited β] (k : α) (j : Nat) (a : α → β)
                                                                (keys : List α) (values : List β) :
  earlier j (butlast (stores a keys values)) k
    = (if occurs k («prefix» j keys) then
         earlier (indexof k («prefix» j keys)) values
       else
         a k) :=
  by sorry

theorem current_shifts (a : Int → Int) (n : Nat) (i : Int) (d : Int)
                       (k : Int) :
  0 ≤ d
    → current (shifts a (butlast (counter i 1 n)) d) k
      = (if i ≤ k ∧ k < i + integer n then a (k + d) else a k) :=
  by sorry

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
  by sorry

-- the same, with the guard and the value on the values of three further dependencies at the iteration of j
-- (from array_mul_init)
theorem current_trace_conditional_store_deps (a0 : Int → Int) (n : Nat)
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
  by sorry

-- the same, at distinct positions ps, which are kept as matched, read by occurs and indexof
-- (from array_monotonic)
theorem current_trace_conditional_store_distinct (a0 : Int → Int)
                                                 (n : Nat) (j : Int)
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
theorem current_trace_cap (a0 : Int → Int) (n : Nat) (j : Int) (b : Int)
                          (hs : List Int) :
  current
    (trace
       a0
       (List.zip (butlast (counter 0 1 n)) hs)
       (fun a ⟨k, h⟩ =>
          if a k < b then a else fun j => if j = k then b else a j))
    j
    = (if 0 ≤ j ∧ j < integer n ∧ b ≤ a0 j then b else a0 j) :=
  by sorry

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
  by sorry

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
  by sorry

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
  by sorry

-- sum, which is linear, and the linear transformations are moved to the outside

theorem sum_empty : sum nil = 0 :=
  by sorry

theorem sum_consts (n : Nat) (x : Int) :
  sum (butlast (consts n x)) = x * integer n :=
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
theorem sum_counter (i : Int) (c : Int) (n : Nat) :
  sum (butlast (counter i c n)) = (2 * i + (integer n - 1) * c) * integer n / 2 :=
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

theorem count_consts {α : Type} [Inhabited α] (n : Nat) (e : α) (v : α) :
  count e (butlast (consts n v)) = (if v = e then integer n else 0) :=
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
theorem count_true_below (m : Int) (i : Int) (n : Nat) :
  i ≤ m ∧ m ≤ i + integer n
    → count True (maps (butlast (counter i 1 n)) (fun k => k < m)) = m - i :=
  by sorry

theorem count_false_below (m : Int) (i : Int) (n : Nat) :
  i ≤ m ∧ m ≤ i + integer n
    → count False (maps (butlast (counter i 1 n)) (fun k => k < m))
      = i + integer n - m :=
  by sorry

theorem count_true_above (m : Int) (i : Int) (n : Nat) :
  i ≤ m ∧ m ≤ i + integer n
    → count True (maps (butlast (counter i 1 n)) (fun k => m ≤ k))
      = i + integer n - m :=
  by sorry

theorem count_false_above (m : Int) (i : Int) (n : Nat) :
  i ≤ m ∧ m ≤ i + integer n
    → count False (maps (butlast (counter i 1 n)) (fun k => m ≤ k)) = m - i :=
  by sorry

theorem count_nonnegative {α : Type} [Inhabited α] (e : α) (vs : List α) :
  0 ≤ count e vs :=
  by sorry

-- the numbers 0, ..., n - 1 with the remainder r modulo m number (n + m - 1 - r) / m
-- (from half, sumt2)
theorem count_remainder (n : Nat) (m : Int) (r : Int) (hs : List Int) :
  0 < m ∧ 0 ≤ r ∧ r < m
    → count
      r
      (maps (List.zip (butlast (counter 0 1 n)) hs) (fun ⟨k, h⟩ => k % m))
      = (integer n + m - 1 - r) / m :=
  by sorry

-- among the truth values of a map over the n iterations, those that are false are the others than those that are
-- true; the dependencies are kept as matched, such that the counts are syntactically equal to those of the program
-- (from sumt2)
theorem count_false_true (i : Int) (c : Int) (n : Nat) (hs : List Int)
                         (P : Int → Int → Prop) :
  count
    False
    (maps (List.zip (butlast (counter i c n)) hs) (fun ⟨k, h⟩ => P k h))
    = integer n
      - count
        True
        (maps (List.zip (butlast (counter i c n)) hs) (fun ⟨k, h⟩ => P k h)) :=
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

theorem current_maxs_earlier (k : Nat) (x : Int) (values : List Int) :
  earlier k values ≤ current (maxs x values) :=
  by sorry

theorem current_mins_initial (x : Int) (values : List Int) :
  current (mins x values) ≤ x :=
  by sorry

theorem current_mins_earlier (k : Nat) (x : Int) (values : List Int) :
  current (mins x values) ≤ earlier k values :=
  by sorry

-- a value that increases by a positive constant in each of its three cases exceeds its initial value after at
-- least one iteration
-- (from large_const)
theorem current_trace_increasing (x0 : Int) (n : Nat) (a : Int) (b : Int)
                                 (c : Int) (hs : List Int)
                                 (C : Int → Prop) (D : Int → Prop)
                                 (E : Int → Prop) :
  n ≠ zero ∧ 0 < a ∧ 0 < b ∧ 0 < c
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
theorem current_trace_bounded (x0 : Int) (n : Nat) (lo : Int) (hi : Int)
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
theorem earlier_above_iterations (n : Nat) (j : Nat) (ts : List Int) :
  above_iterations n ts ∧ integer j < integer n
    → (integer j < earlier j ts ↔ True) :=
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
theorem sum_squares (n : Nat) :
  sum (maps (butlast (counter 0 1 n)) (fun k => 3 * k * k))
    = integer n * integer n * integer n - integer n
      - 3 * ((-integer n + integer n * integer n) / 2) :=
  by sorry

-- a power of 2 is not divisible by 3
-- (from underapprox_1-1, underapprox_1-2)
theorem pow_two_mod_three (n : Nat) : pow 2 n % 3 = 0 ↔ False :=
  by sorry

-- a nonnegative factor cancels in a strict comparison; does not match a literal coefficient (see TODO.md)
-- (from count_by_k)
theorem mul_lt_cancel (k : Int) (a : Int) (b : Int) :
  0 ≤ k → (k * a < k * b ↔ 0 < k ∧ a < b) :=
  by sorry

-- counterexamples: lemmas that hold only under further assumptions, which the contexts of the goals of -teq
-- provide, e.g. a prefix that is not longer than the other one, or a nonempty list

-- prefix_prefix for j > k
example : ¬ («prefix» 2 («prefix» 1 [(1 : Int), 2]) = «prefix» 2 [1, 2]) :=
  by simp [«prefix»]

-- occurs_earlier for the empty sequence
example : ¬ (occurs (earlier 0 ([] : List Int)) []) :=
  by simp [occurs]

end TEQ
