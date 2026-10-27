// strides: the reads of the final arrays of loops that store several cells per iteration, at strided positions (s k, s
// k + 1, ...) or ahead of the iteration (k + 1, then k), from the MonoCera benchmarks; an optional module over teq.dfy
// (-include teq:strides); unlike the other modules, these lemmas fix the number of stores and of cases on their
// left-hand sides, since a rule matches a fixed shape of nested stores

// a loop whose iteration k stores X at 2 k and Y at 2 k + 1 writes disjoint pairs of cells, which cover
// 0, ..., 2 n - 1;
// X and Y do not depend on the iteration, since variables of the rule do not capture the bound variables
// (from MonoCera: array_doub_access_init_const, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} select_current_trace_stride2(a0: array<int, int>, n: int, X: int, Y: int, j: int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: a[2 * k := X][2 * k + 1 := Y]))[j]
      == if 0 <= j && j < 2 * n then (if j % 2 == 0 then X else Y) else a0[j]

// the same for stride 3, the triples 3 k, 3 k + 1, 3 k + 2 cover 0, ..., 3 n - 1
// (from MonoCera: array_tripl_access_init_const, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} select_current_trace_stride3(a0: array<int, int>, n: int, X: int, Y: int, Z: int, j: int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k :: a[3 * k := X][3 * k + 1 := Y][3 * k + 2 := Z]))[j]
      == if 0 <= j && j < 3 * n then (if j % 3 == 0 then X else if j % 3 == 1 then Y else Z) else a0[j]

// the same as stride 2 with three cases whose guards do not depend on the iteration, e.g. on MINVAL, and are
// exhaustive, such that one of the pairs is stored in all iterations; pr3-pr5 have 2^s cases of s stores each, one
// per combination of the guards of the cells, which this shape does not cover
// (from MonoCera: pr2, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} select_current_trace_stride2_cases(a0: array<int, int>, n: int, P: bool, Q: bool, R: bool,
    X1: int, Y1: int, X2: int, Y2: int, X3: int, Y3: int, j: int)
  requires R == (!P && !Q)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k ::
                  case P => a[2 * k := X1][2 * k + 1 := Y1]
                  case Q => a[2 * k := X2][2 * k + 1 := Y2]
                  case R => a[2 * k := X3][2 * k + 1 := Y3]))[j]
      == if 0 <= j && j < 2 * n
         then
           if j % 2 == 0 then (if P then X1 else if Q then X2 else X3)
           else (if P then Y1 else if Q then Y2 else Y3)
         else a0[j]

// the same for stride 3 with 4 cases, one per threshold of the guards of the 3 cells (from MonoCera: pr3)
lemma {:rw} {:teq} select_current_trace_stride3_cases4(a0: array<int, int>, n: int, P1: bool, P2: bool, P3: bool,
    P4: bool, X1_0: int, X1_1: int, X1_2: int, X2_0: int, X2_1: int, X2_2: int, X3_0: int, X3_1: int, X3_2: int,
    X4_0: int, X4_1: int, X4_2: int, j: int)
  requires P4 == (!P1 && !P2 && !P3)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k ::
                  case P1 => a[3 * k := X1_0][3 * k + 1 := X1_1][3 * k + 2 := X1_2]
                  case P2 => a[3 * k := X2_0][3 * k + 1 := X2_1][3 * k + 2 := X2_2]
                  case P3 => a[3 * k := X3_0][3 * k + 1 := X3_1][3 * k + 2 := X3_2]
                  case P4 => a[3 * k := X4_0][3 * k + 1 := X4_1][3 * k + 2 := X4_2]))[j]
      == if 0 <= j && j < 3 * n
         then
           if j % 3 == 0 then (if P1 then X1_0 else if P2 then X2_0 else if P3 then X3_0 else X4_0)
           else if j % 3 == 1 then (if P1 then X1_1 else if P2 then X2_1 else if P3 then X3_1 else X4_1)
           else (if P1 then X1_2 else if P2 then X2_2 else if P3 then X3_2 else X4_2)
         else a0[j]

// the same for stride 4 with 5 cases, one per threshold of the guards of the 4 cells (from MonoCera: pr4)
lemma {:rw} {:teq} select_current_trace_stride4_cases5(a0: array<int, int>, n: int, P1: bool, P2: bool, P3: bool,
    P4: bool, P5: bool, X1_0: int, X1_1: int, X1_2: int, X1_3: int, X2_0: int, X2_1: int, X2_2: int, X2_3: int,
    X3_0: int, X3_1: int, X3_2: int, X3_3: int, X4_0: int, X4_1: int, X4_2: int, X4_3: int, X5_0: int, X5_1: int,
    X5_2: int, X5_3: int, j: int)
  requires P5 == (!P1 && !P2 && !P3 && !P4)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k ::
                  case P1 => a[4 * k := X1_0][4 * k + 1 := X1_1][4 * k + 2 := X1_2][4 * k + 3 := X1_3]
                  case P2 => a[4 * k := X2_0][4 * k + 1 := X2_1][4 * k + 2 := X2_2][4 * k + 3 := X2_3]
                  case P3 => a[4 * k := X3_0][4 * k + 1 := X3_1][4 * k + 2 := X3_2][4 * k + 3 := X3_3]
                  case P4 => a[4 * k := X4_0][4 * k + 1 := X4_1][4 * k + 2 := X4_2][4 * k + 3 := X4_3]
                  case P5 => a[4 * k := X5_0][4 * k + 1 := X5_1][4 * k + 2 := X5_2][4 * k + 3 := X5_3]))[j]
      == if 0 <= j && j < 4 * n
         then
           if j % 4 == 0 then (if P1 then X1_0 else if P2 then X2_0 else if P3 then X3_0 else if P4 then X4_0 else X5_0)
           else if j % 4 == 1 then (if P1 then X1_1 else if P2 then X2_1 else if P3 then X3_1 else if P4 then X4_1
                                    else X5_1)
           else if j % 4 == 2 then (if P1 then X1_2 else if P2 then X2_2 else if P3 then X3_2 else if P4 then X4_2
                                    else X5_2)
           else (if P1 then X1_3 else if P2 then X2_3 else if P3 then X3_3 else if P4 then X4_3 else X5_3)
         else a0[j]

// the same for stride 5 with 6 cases, one per threshold of the guards of the 5 cells (from MonoCera: pr5)
lemma {:rw} {:teq} select_current_trace_stride5_cases6(a0: array<int, int>, n: int, P1: bool, P2: bool, P3: bool,
    P4: bool, P5: bool, P6: bool, X1_0: int, X1_1: int, X1_2: int, X1_3: int, X1_4: int, X2_0: int, X2_1: int,
    X2_2: int, X2_3: int, X2_4: int, X3_0: int, X3_1: int, X3_2: int, X3_3: int, X3_4: int, X4_0: int, X4_1: int,
    X4_2: int, X4_3: int, X4_4: int, X5_0: int, X5_1: int, X5_2: int, X5_3: int, X5_4: int, X6_0: int, X6_1: int,
    X6_2: int, X6_3: int, X6_4: int, j: int)
  requires P6 == (!P1 && !P2 && !P3 && !P4 && !P5)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋ do a, k ::
                  case P1 => a[5 * k := X1_0][5 * k + 1 := X1_1][5 * k + 2 := X1_2][5 * k + 3 := X1_3]
                              [5 * k + 4 := X1_4]
                  case P2 => a[5 * k := X2_0][5 * k + 1 := X2_1][5 * k + 2 := X2_2][5 * k + 3 := X2_3]
                              [5 * k + 4 := X2_4]
                  case P3 => a[5 * k := X3_0][5 * k + 1 := X3_1][5 * k + 2 := X3_2][5 * k + 3 := X3_3]
                              [5 * k + 4 := X3_4]
                  case P4 => a[5 * k := X4_0][5 * k + 1 := X4_1][5 * k + 2 := X4_2][5 * k + 3 := X4_3]
                              [5 * k + 4 := X4_4]
                  case P5 => a[5 * k := X5_0][5 * k + 1 := X5_1][5 * k + 2 := X5_2][5 * k + 3 := X5_3]
                              [5 * k + 4 := X5_4]
                  case P6 => a[5 * k := X6_0][5 * k + 1 := X6_1][5 * k + 2 := X6_2][5 * k + 3 := X6_3]
                              [5 * k + 4 := X6_4]))[j]
      == if 0 <= j && j < 5 * n
         then
           if j % 5 == 0 then (if P1 then X1_0 else if P2 then X2_0 else if P3 then X3_0 else if P4 then X4_0
                               else if P5 then X5_0 else X6_0)
           else if j % 5 == 1 then (if P1 then X1_1 else if P2 then X2_1 else if P3 then X3_1 else if P4 then X4_1
                                    else if P5 then X5_1 else X6_1)
           else if j % 5 == 2 then (if P1 then X1_2 else if P2 then X2_2 else if P3 then X3_2 else if P4 then X4_2
                                    else if P5 then X5_2 else X6_2)
           else if j % 5 == 3 then (if P1 then X1_3 else if P2 then X2_3 else if P3 then X3_3 else if P4 then X4_3
                                    else if P5 then X5_3 else X6_3)
           else (if P1 then X1_4 else if P2 then X2_4 else if P3 then X3_4 else if P4 then X4_4 else if P5 then X5_4
                 else X6_4)
         else a0[j]

// stride 2 with values read in the iteration, each kept unless it is the default c, which stores d instead: the first
// cell takes x, the second y if x is not the default and z otherwise (a value read again), the four cases of the two
// conditionals; read at j from the choices of the iteration j / 2
// (from MonoCera: pnr2)
lemma {:rw} {:teq} select_current_trace_stride2_defaults(a0: array<int, int>, n: int, c: int, d: int, xs: List<int>,
    ys: List<int>, zs: List<int>, j: int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, xs, ys, zs do a, k, x, y, z ::
                  case x != c && y != c => a[2 * k := x][2 * k + 1 := y]
                  case x != c && y == c => a[2 * k := x][2 * k + 1 := d]
                  case x == c && z != c => a[2 * k := d][2 * k + 1 := z]
                  case x == c && z == c => a[2 * k := d][2 * k + 1 := d]))[j]
      == if 0 <= j && j < 2 * n
         then (if j % 2 == 0
               then (if earlier(j / 2, xs) != c then earlier(j / 2, xs) else d)
               else (if earlier(j / 2, xs) != c
                     then (if earlier(j / 2, ys) != c then earlier(j / 2, ys) else d)
                     else (if earlier(j / 2, zs) != c then earlier(j / 2, zs) else d)))
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
