import Mathlib

namespace HassinRSP.Rounding

/-- An instance of the restricted shortest path problem (Hassin 1992, §1, p. 36): `n` vertices
`1, …, n`, a set `E` of directed edges `(i, j)`, an integer length `c (i, j)` and an integer
transition time `t (i, j)` on every edge. -/
structure Instance where
  /-- the number of vertices; the vertex set is `{1, …, n}` -/
  n : ℕ
  /-- the edge set -/
  E : Finset (ℕ × ℕ)
  /-- the length `c_ij` of the edge `(i, j)` -/
  c : ℕ × ℕ → ℕ
  /-- the transition time `t_ij` of the edge `(i, j)` -/
  t : ℕ × ℕ → ℕ

/-- The standing assumptions of §1–§2 (pp. 36–37): at least two vertices, every edge `(i, j)`
has `1 ≤ i < j ≤ n` (the acyclic numbering "(i, j) ∈ E implies i < j"), and lengths and
transition times are positive integers. -/
def Instance.WellFormed (I : Instance) : Prop :=
  2 ≤ I.n ∧ (∀ e ∈ I.E, 1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ I.n) ∧ (∀ e ∈ I.E, 0 < I.c e ∧ 0 < I.t e)

/-- `p` is a directed `i`–`j` path using only edges of `F`: a nonempty list of vertices starting
at `i`, ending at `j`, with every consecutive pair an edge of `F`. -/
def IsPathIn (F : Finset (ℕ × ℕ)) (i j : ℕ) (p : List ℕ) : Prop :=
  p.head? = some i ∧ p.getLast? = some j ∧ p.IsChain (fun a b => (a, b) ∈ F)

/-- The length `c(p)` of a path: the sum of the lengths of its edges. -/
def pathLen (I : Instance) (p : List ℕ) : ℕ :=
  ((p.zip p.tail).map I.c).sum

/-- The transition time `t(p)` of a path: the sum of the transition times of its edges. -/
def pathTime (I : Instance) (p : List ℕ) : ℕ :=
  ((p.zip p.tail).map I.t).sum

/-- A `1`–`n` `T`-path: a `1`–`n` path in `E` whose transition time is at most `T`. -/
def IsTPath (I : Instance) (T : ℕ) (p : List ℕ) : Prop :=
  IsPathIn I.E 1 I.n p ∧ pathTime I p ≤ T

/-- The rounded length `⌊c_ij (n − 1) / (V ε)⌋` of an edge (§3, Procedure TEST(V), Step 1, p. 38;
at `V = LB` it is Step 2 of the Rounding Algorithm, §4, p. 39). -/
noncomputable def roundLen (I : Instance) (ε V : ℝ) (e : ℕ × ℕ) : ℕ :=
  ⌊(I.c e : ℝ) * ((I.n : ℝ) - 1) / (V * ε)⌋₊

/-- The rounded length of a path: the sum of the rounded lengths of its edges. -/
noncomputable def roundPathLen (I : Instance) (ε V : ℝ) (p : List ℕ) : ℕ :=
  ((p.zip p.tail).map (roundLen I ε V)).sum

/-- TEST(V), Step 1: the edges kept, those with `c_ij ≤ V`. -/
noncomputable def prunedE (I : Instance) (V : ℝ) : Finset (ℕ × ℕ) :=
  I.E.filter (fun e => (I.c e : ℝ) ≤ V)

/-- TEST(V) outputs NO: for some integer `c < (n − 1)/ε` there is a `1`–`n` path in the pruned
graph of transition time at most `T` and rounded length at most `c` (that is, `g_n(c) ≤ T`). -/
def testNo (I : Instance) (T : ℕ) (ε V : ℝ) : Prop :=
  ∃ c : ℕ, (c : ℝ) < ((I.n : ℝ) - 1) / ε ∧
    ∃ p, IsPathIn (prunedE I V) 1 I.n p ∧ pathTime I p ≤ T ∧ roundPathLen I ε V p ≤ c

/-- TEST(V) outputs YES: Step 2 reaches `c ≥ (n − 1)/ε` without finding `g_n(c) ≤ T`. -/
def testYes (I : Instance) (T : ℕ) (ε V : ℝ) : Prop :=
  ¬ testNo I T ε V

open Classical in
/-- One pass of Step 1 of the Rounding Algorithm (§4, p. 39) on the bounds `b = (LB, UB)`:
if `UB ≤ 2 LB` the bounds are kept (the algorithm goes to Step 2); otherwise `V = (LB · UB)^{1/2}`
and `LB ← V` if TEST(V) = YES, `UB ← V (1 + ε)` if TEST(V) = NO. -/
noncomputable def roundingStep (I : Instance) (T : ℕ) (ε : ℝ) (b : ℝ × ℝ) : ℝ × ℝ :=
  if b.2 ≤ 2 * b.1 then b
  else if testYes I T ε (Real.sqrt (b.1 * b.2)) then (Real.sqrt (b.1 * b.2), b.2)
  else (b.1, Real.sqrt (b.1 * b.2) * (1 + ε))

/-- The bounds `(LB, UB)` after `k` passes of Step 1, starting from `(LB0, UB0)` (Step 0). -/
noncomputable def roundingRun (I : Instance) (T : ℕ) (ε : ℝ) (LB0 UB0 : ℝ) (k : ℕ) : ℝ × ℝ :=
  (roundingStep I T ε)^[k] (LB0, UB0)

/-- Step 2 of the Rounding Algorithm: `p` is a `T`-path that is shortest among all `T`-paths for
the rounded lengths `⌊c_ij (n − 1) / (ε LB)⌋`. -/
def IsRoundingOutput (I : Instance) (T : ℕ) (ε LB : ℝ) (p : List ℕ) : Prop :=
  IsTPath I T p ∧ ∀ q, IsTPath I T q → roundPathLen I ε LB p ≤ roundPathLen I ε LB q

/-- The sum of the `n − 1` longest edge-lengths (§4, Step 0, p. 39): the largest total length of
a set of at most `n − 1` edges. -/
def sumLongest (I : Instance) : ℕ :=
  (I.E.powerset.filter (fun F => F.card ≤ I.n - 1)).sup (fun F => ∑ e ∈ F, I.c e)

/-- `g_j(c)` (§2, Algorithm B): the time of a quickest `1`–`j` path whose length is at most `c`,
`⊤ = ∞` if there is none. -/
noncomputable def quickestTime (I : Instance) (j c : ℕ) : ℕ∞ :=
  ⨅ (p : List ℕ) (_ : IsPathIn I.E 1 j p ∧ pathLen I p ≤ c), (pathTime I p : ℕ∞)

/-- `f_j(t)` (§2, Algorithm A): the length of a shortest `1`–`j` `t`-path, `⊤ = ∞` if there is
none. -/
noncomputable def shortestLen (I : Instance) (j t : ℕ) : ℕ∞ :=
  ⨅ (p : List ℕ) (_ : IsPathIn I.E 1 j p ∧ pathTime I p ≤ t), (pathLen I p : ℕ∞)

/-- Algorithm B's recursion (§2, pp. 37–38), `algB I c j = g_j(c)`:
`g_1(c) = 0`; `g_j(0) = ∞` for `j ≠ 1`; and for `c ≥ 1`
`g_j(c) = min{g_j(c − 1), min_{(k, j) ∈ E, c_kj ≤ c} (g_k(c − c_kj) + t_kj)}`.
Edges with `c_kj = 0` are skipped (none exist on a well-formed instance). -/
noncomputable def algB (I : Instance) (c j : ℕ) : ℕ∞ :=
  if j = 1 then 0
  else if _hc : c = 0 then ⊤
  else min (algB I (c - 1) j)
    (I.E.inf (fun e => if _h : e.2 = j ∧ 1 ≤ I.c e ∧ I.c e ≤ c
      then algB I (c - I.c e) e.1 + (I.t e : ℕ∞) else ⊤))
termination_by c
decreasing_by all_goals omega

/-- Algorithm A's recursion (§2, p. 37), `algA I t j = f_j(t)`:
`f_1(t) = 0`; `f_j(0) = ∞` for `j ≠ 1`; and for `t ≥ 1`
`f_j(t) = min{f_j(t − 1), min_{(k, j) ∈ E, t_kj ≤ t} (f_k(t − t_kj) + c_kj)}`.
Edges with `t_kj = 0` are skipped (none exist on a well-formed instance). -/
noncomputable def algA (I : Instance) (t j : ℕ) : ℕ∞ :=
  if j = 1 then 0
  else if _ht : t = 0 then ⊤
  else min (algA I (t - 1) j)
    (I.E.inf (fun e => if _h : e.2 = j ∧ 1 ≤ I.t e ∧ I.t e ≤ t
      then algA I (t - I.t e) e.1 + (I.c e : ℕ∞) else ⊤))
termination_by t
decreasing_by all_goals omega

end HassinRSP.Rounding
