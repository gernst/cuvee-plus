// strides: the stores of loops that store several adjacent cells per iteration, at strided positions (s k + o,
// s k + o + 1, ...) or ahead of the iteration (k + 1, then k), from the MonoCera benchmarks; an optional module over
// teq.dfy (-include teq:strides); the stores of 2 to 5 adjacent cells are folds with one list of values per cell, which
// the matcher synthesizes as maps, with the cases of the update if the values differ between them, e.g. one case per
// combination of the guards of conditional stores

// the stores of the values xs₀, xs₁, ... at the positions p, p + 1, ... for the positions p of keys
function {:teq} {:fold} strides₂(a: array<int, int>, keys: List<int>, xs₀: List<int>, xs₁: List<int>):
    Trace<array<int, int>>
{
  trace(a, for keys, xs₀, xs₁ do b, p, x₀, x₁ :: b[p := x₀][p + 1 := x₁])
}

function {:teq} {:fold} strides₃(a: array<int, int>, keys: List<int>, xs₀: List<int>, xs₁: List<int>,
    xs₂: List<int>): Trace<array<int, int>>
{
  trace(a, for keys, xs₀, xs₁, xs₂ do b, p, x₀, x₁, x₂ :: b[p := x₀][p + 1 := x₁][p + 2 := x₂])
}

function {:teq} {:fold} strides₄(a: array<int, int>, keys: List<int>, xs₀: List<int>, xs₁: List<int>,
    xs₂: List<int>, xs₃: List<int>): Trace<array<int, int>>
{
  trace(a, for keys, xs₀, xs₁, xs₂, xs₃ do b, p, x₀, x₁, x₂, x₃ ::
    b[p := x₀][p + 1 := x₁][p + 2 := x₂][p + 3 := x₃])
}

function {:teq} {:fold} strides₅(a: array<int, int>, keys: List<int>, xs₀: List<int>, xs₁: List<int>,
    xs₂: List<int>, xs₃: List<int>, xs₄: List<int>): Trace<array<int, int>>
{
  trace(a, for keys, xs₀, xs₁, xs₂, xs₃, xs₄ do b, p, x₀, x₁, x₂, x₃, x₄ ::
    b[p := x₀][p + 1 := x₁][p + 2 := x₂][p + 3 := x₃][p + 4 := x₄])
}

// the windows of the iterations are disjoint for a stride s of at least their width, the cell j belongs to the
// iteration (j - o) / s, at the position (j - o) % s of its window, or to no window
lemma {:rw} {:teq} select_current_strides₂(a0: array<int, int>, o: int, s: int, n: int, xs₀: List<int>,
    xs₁: List<int>, j: int)
  requires 2 <= s
  ensures current(strides₂(a0, ⌊counter(o, s, n)⌋, xs₀, xs₁))[j]
    == if 0 <= j - o && j - o < s * n && (j - o) % s < 2
       then (if (j - o) % s == 0 then earlier((j - o) / s, xs₀) else earlier((j - o) / s, xs₁))
       else a0[j]

lemma {:rw} {:teq} select_current_strides₃(a0: array<int, int>, o: int, s: int, n: int, xs₀: List<int>,
    xs₁: List<int>, xs₂: List<int>, j: int)
  requires 3 <= s
  ensures current(strides₃(a0, ⌊counter(o, s, n)⌋, xs₀, xs₁, xs₂))[j]
    == if 0 <= j - o && j - o < s * n && (j - o) % s < 3
       then (if (j - o) % s == 0 then earlier((j - o) / s, xs₀)
             else if (j - o) % s == 1 then earlier((j - o) / s, xs₁)
             else earlier((j - o) / s, xs₂))
       else a0[j]

lemma {:rw} {:teq} select_current_strides₄(a0: array<int, int>, o: int, s: int, n: int, xs₀: List<int>,
    xs₁: List<int>, xs₂: List<int>, xs₃: List<int>, j: int)
  requires 4 <= s
  ensures current(strides₄(a0, ⌊counter(o, s, n)⌋, xs₀, xs₁, xs₂, xs₃))[j]
    == if 0 <= j - o && j - o < s * n && (j - o) % s < 4
       then (if (j - o) % s == 0 then earlier((j - o) / s, xs₀)
             else if (j - o) % s == 1 then earlier((j - o) / s, xs₁)
             else if (j - o) % s == 2 then earlier((j - o) / s, xs₂)
             else earlier((j - o) / s, xs₃))
       else a0[j]

lemma {:rw} {:teq} select_current_strides₅(a0: array<int, int>, o: int, s: int, n: int, xs₀: List<int>,
    xs₁: List<int>, xs₂: List<int>, xs₃: List<int>, xs₄: List<int>, j: int)
  requires 5 <= s
  ensures current(strides₅(a0, ⌊counter(o, s, n)⌋, xs₀, xs₁, xs₂, xs₃, xs₄))[j]
    == if 0 <= j - o && j - o < s * n && (j - o) % s < 5
       then (if (j - o) % s == 0 then earlier((j - o) / s, xs₀)
             else if (j - o) % s == 1 then earlier((j - o) / s, xs₁)
             else if (j - o) % s == 2 then earlier((j - o) / s, xs₂)
             else if (j - o) % s == 3 then earlier((j - o) / s, xs₃)
             else earlier((j - o) / s, xs₄))
       else a0[j]

// a loop whose iteration k stores F(k) at k + 1 and then G(k) at k, except in the last one, k + 1 == m, which stores
// at k only, leaves G(j) at j < n, since the iteration j writes it last; at n, there is F(n - 1) if n < m, the guards
// cover all iterations only for n <= m
// (from MonoCera: rewnif; used on SV-COMP by rew, rewnif only)
lemma {:rw} {:teq} select_current_trace_ahead(a0: array<int, int>, n: int, m: int, F: (int) -> int, G: (int) -> int,
    j: int)
  requires n <= m
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k ::
                  case k + 1 < m => a[k + 1 := F(k)][k := G(k)]
                  case m == k + 1 => a[k := G(k)]))[j]
      == if 0 <= j && j < n then G(j)
         else if j == n && 0 < j && j < m then F(j - 1)
         else a0[j]

// the same for a loop down from s, whose iteration i stores F(i) at i - 1, if 1 <= i, and then G(i) at i: the cells
// s - n + 1, ..., s hold G, the cell below the last iteration the value stored ahead by it
// (from MonoCera: rewnifrev, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} select_current_trace_ahead_down(a0: array<int, int>, n: int, s: int, F: (int) -> int,
    G: (int) -> int, j: int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(s, -1, n)⌋ do a, k, i ::
                  case 1 <= i => a[i + (-1) := F(i)][i := G(i)]
                  case i < 1 => a[i := G(i)]))[j]
      == if s - n < j && j <= s then G(j)
         else if j == s - n && 0 <= j && 0 < n then F(j + 1)
         else a0[j]
