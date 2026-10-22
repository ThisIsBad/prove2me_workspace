import Mathlib

namespace MaxPressure.ReversedLeontief

/-!
Dai and Lin (2005), *Maximum pressure policies in stochastic processing networks*,
§§2–3 (pp. 199–201), §7 (pp. 206–207), §8 (p. 208) and Appendix B (p. 215).

Index conventions. Internal buffers `1,…,I` are `Fin I`; buffers `0,…,I` (with the outside
Buffer 0) are `Fin (I + 1)`, Buffer 0 being `0` and internal buffer `i : Fin I` being `i.succ`.
Activities `1,…,J` are `Fin J` and processors `1,…,K` are `Fin K` (the paper's 1-based labels
shifted to 0-based `Fin`). The idle "Activity 0" of §8 and (60) is `none : Option (Fin J)`, and
activity `j` is `some j`.
-/

/-- Network data of §§2.1–2.3 and 2.5 (pp. 199–200): resource consumption matrix `A`,
constituency indicators `B` (column `0` is Buffer 0), the set of input processors, mean
processing requirements `m j` of (3) and routing matrices `P j` of (4). -/
structure Network (I J K : ℕ) where
  A : Matrix (Fin K) (Fin J) ℝ
  B : Matrix (Fin J) (Fin (I + 1)) ℝ
  inputProc : Fin K → Prop
  m : Fin J → ℝ
  P : Fin J → Matrix (Fin (I + 1)) (Fin (I + 1)) ℝ

/-- Activity `j` is an input activity: its constituency is `{0}` (p. 199). -/
def IsInputActivity {I J K : ℕ} (N : Network I J K) (j : Fin J) : Prop :=
  N.B j 0 = 1 ∧ ∀ i : Fin I, N.B j i.succ = 0

/-- Activity `j` is a service activity: Buffer 0 is not in its constituency (p. 199). -/
def IsServiceActivity {I J K : ℕ} (N : Network I J K) (j : Fin J) : Prop :=
  N.B j 0 = 0

/-- Standing assumptions of §2 (pp. 199–200). Two clauses are disclosed additions: every input
processor has at least one activity (without it, (2) is infeasible and `𝒜 = ∅`), and `0 < m j`
(without it, `μ_j = 1/m_j` is not defined). The row sums of `P j` are not imposed. -/
def Network.Standing {I J K : ℕ} (N : Network I J K) : Prop :=
  (∀ k j, N.A k j = 0 ∨ N.A k j = 1) ∧
  (∀ j i, N.B j i = 0 ∨ N.B j i = 1) ∧
  (∀ j, ∃ i, N.B j i = 1) ∧
  (∀ j, IsInputActivity N j ∨ IsServiceActivity N j) ∧
  (∀ j, ∃ k, N.A k j = 1) ∧
  (∀ k j, N.A k j = 1 → (N.inputProc k ↔ IsInputActivity N j)) ∧
  (∃ j, IsInputActivity N j) ∧
  (∀ k, N.inputProc k → ∃ j, N.A k j = 1) ∧
  (∀ j, 0 < N.m j) ∧
  (∀ j i i', 0 ≤ N.P j i i') ∧
  (∀ j, N.P j 0 0 = 0)

/-- Processing rate `μ_j = 1/m_j` (p. 200). -/
noncomputable def mu {I J K : ℕ} (N : Network I J K) (j : Fin J) : ℝ :=
  1 / N.m j

/-- Input-output matrix (5), p. 201:
`R_ij = μ_j (B_ji − ∑_{i' ∈ ℐ ∪ {0}} B_ji' P^j_{i'i})`, for internal buffers `i`. -/
noncomputable def R {I J K : ℕ} (N : Network I J K) : Matrix (Fin I) (Fin J) ℝ :=
  fun i j => mu N j * (N.B j i.succ - ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ)

/-- The allocation set `𝒜` (p. 200): `a ∈ ℝ^J_+` satisfying (1) `∑_j A_kj a_j ≤ 1` for every
processor and (2) `∑_j A_kj a_j = 1` for every input processor. -/
def allocSet {I J K : ℕ} (N : Network I J K) : Set (Fin J → ℝ) :=
  {a | (∀ j, 0 ≤ a j) ∧
    (∀ k, ∑ j, N.A k j * a j ≤ 1) ∧
    (∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1)}

/-- The extreme allocations `ℰ`: the extreme points of `𝒜` (p. 200). -/
def extremeAllocs {I J K : ℕ} (N : Network I J K) : Set (Fin J → ℝ) :=
  Set.extremePoints ℝ (allocSet N)

/-- Total network pressure (6), p. 201: `p(a, z) = z · R a`. -/
noncomputable def pressure {I J K : ℕ} (N : Network I J K)
    (a : Fin J → ℝ) (z : Fin I → ℝ) : ℝ :=
  dotProduct z (Matrix.mulVec (R N) a)

/-- Definition 5, p. 207: the network is *reversed Leontief* if each activity requires
exactly one processor. -/
def IsReversedLeontief {I J K : ℕ} (N : Network I J K) : Prop :=
  ∀ j, ∃! k, N.A k j = 1

/-- The integer allocations `𝒩` (§7, p. 206): allocations `a ∈ ℤ^J_+` satisfying (1) and (2),
i.e. the members of `𝒜` all of whose coordinates are natural numbers. -/
def intAllocs {I J K : ℕ} (N : Network I J K) : Set (Fin J → ℝ) :=
  {a | a ∈ allocSet N ∧ ∀ j, ∃ n : ℕ, a j = n}

/-- Activity `j` pressure (30), p. 208: `p(j, z) = ∑_{i ∈ ℐ} R_ij z_i`. -/
noncomputable def actPressure {I J K : ℕ} (N : Network I J K)
    (j : Fin J) (z : Fin I → ℝ) : ℝ :=
  ∑ i, R N i j * z i

/-- Activity pressure with the idle Activity 0 (`none`), whose pressure is `0` (p. 208). -/
noncomputable def actPressure' {I J K : ℕ} (N : Network I J K)
    (o : Option (Fin J)) (z : Fin I → ℝ) : ℝ :=
  match o with
  | none => 0
  | some j => actPressure N j z

/-- The possible activities `𝒥(k)` of processor `k`, (60), p. 215:
`{j : A_kj = 1}` for an input processor, `{0} ∪ {j : A_kj = 1}` for a service processor;
the idle Activity 0 is `none`. -/
def procActs {I J K : ℕ} (N : Network I J K) (k : Fin K) : Set (Option (Fin J)) :=
  {o | (o = none ∧ ¬ N.inputProc k) ∨ ∃ j, o = some j ∧ N.A k j = 1}

open Classical in
/-- `j_k(a)` (p. 208): the activity processor `k` works on under the integer allocation `a`,
and `none` (Activity 0) if `k` is idle. It picks some `j` with `A_kj = 1` and `a_j = 1`; on an
integer allocation of a reversed Leontief network there is at most one such `j` (by (1)), so the
choice is unique there. The value is not meaningful for fractional allocations, and no statement
of this mission uses it on them. -/
noncomputable def activityOf {I J K : ℕ} (N : Network I J K)
    (a : Fin J → ℝ) (k : Fin K) : Option (Fin J) :=
  if h : ∃ j, N.A k j = 1 ∧ a j = 1 then some h.choose else none

/-- The allocation `b^o` of the proof of Lemma 1 (p. 215) for a processor `k` and a possible
activity `o ∈ 𝒥(k)`: activities not requiring `k` keep their level `a_{j'}`, and processor `k`
employs activity `o` at a 100% level (all its other activities at level 0; none of them when
`o` is the idle Activity 0). -/
noncomputable def splitAlloc {I J K : ℕ} (N : Network I J K)
    (a : Fin J → ℝ) (k : Fin K) (o : Option (Fin J)) : Fin J → ℝ :=
  fun j' => if N.A k j' = 1 then (if o = some j' then 1 else 0) else a j'

/-- The unit vector `e_j` of p. 208 for activity `some j`, and the zero vector for the idle
Activity 0 (`none`), as needed for `e_{j_k(a)}` when processor `k` is idle. -/
noncomputable def unitVec {J : ℕ} (o : Option (Fin J)) : Fin J → ℝ :=
  match o with
  | none => 0
  | some j => Pi.single j 1

end MaxPressure.ReversedLeontief
