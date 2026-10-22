import Mathlib

namespace MaxPressure.StrictLeontief

/-! Dai and Lin (2005), *Maximum pressure policies in stochastic processing networks*,
Oper. Res. 53(2), §2 (pp. 199–200), §3 ((5), (6), p. 201), §4 (Assumption 1, p. 202) and
§6.1 (p. 204).

Indexing: the paper's internal buffers `1, …, I` are `Fin I`; buffers `0, …, I` are
`Fin (I + 1)`, with the outside Buffer 0 represented by `0` and internal buffer `i : Fin I`
by `i.succ`. Activities `1, …, J` are `Fin J` and processors `1, …, K` are `Fin K`
(0-based labels). -/

/-- Network data of §§2.1–2.3, 2.5: the resource consumption matrix `A` (`A k j = 1` iff
activity `j` needs processor `k`), the constituency indicator `B` (`B j i = 1` iff activity
`j` processes buffer `i`; column `0` is Buffer 0), the input processors, the mean
processing requirements `m j` of (3) and the routing matrices `P j` of (4). -/
structure Network (I J K : ℕ) where
  A : Matrix (Fin K) (Fin J) ℝ
  B : Matrix (Fin J) (Fin (I + 1)) ℝ
  inputProc : Fin K → Prop
  m : Fin J → ℝ
  P : Fin J → Matrix (Fin (I + 1)) (Fin (I + 1)) ℝ

/-- Activity `j` is an input activity: its constituency is `{0}`. -/
def IsInputActivity {I J K : ℕ} (N : Network I J K) (j : Fin J) : Prop :=
  N.B j 0 = 1 ∧ ∀ i : Fin I, N.B j i.succ = 0

/-- Activity `j` is a service activity: Buffer 0 is not in its constituency. -/
def IsServiceActivity {I J K : ℕ} (N : Network I J K) (j : Fin J) : Prop :=
  N.B j 0 = 0

/-- The standing assumptions of §2 (pp. 199–200). The last-but-three clause (every input
processor has an activity) and `0 < m j` are disclosed necessary readings of the page:
"the input processors are never idle" presupposes the first, and `μ_j = 1/m_j` the second.
`P j ≥ 0` and `P j 0 0 = 0` come from `Φ^j_{00} = 0` and (4). -/
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

/-- The input-output matrix (5), p. 201:
`R_ij = μ_j (B_ji − Σ_{i' ∈ ℐ ∪ {0}} B_{ji'} P^j_{i'i})`, for internal buffers `i`. -/
noncomputable def R {I J K : ℕ} (N : Network I J K) :
    Matrix (Fin I) (Fin J) ℝ :=
  fun i j => mu N j * (N.B j i.succ - ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ)

/-- The allocation set `𝒜` of (1)–(2), p. 200: nonnegative `a` with `Aa ≤ e` and equality
at every input processor. -/
def allocSet {I J K : ℕ} (N : Network I J K) : Set (Fin J → ℝ) :=
  {a | (∀ j, 0 ≤ a j) ∧
    (∀ k, ∑ j, N.A k j * a j ≤ 1) ∧
    (∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1)}

/-- The extreme allocations `ℰ`: the extreme points of `𝒜` (p. 200). -/
def extremeAllocs {I J K : ℕ} (N : Network I J K) : Set (Fin J → ℝ) :=
  Set.extremePoints ℝ (allocSet N)

/-- The network pressure (6), p. 201: `p(a, z) = z · Ra`. -/
noncomputable def pressure {I J K : ℕ} (N : Network I J K)
    (a : Fin J → ℝ) (z : Fin I → ℝ) : ℝ :=
  dotProduct z (Matrix.mulVec (R N) a)

/-- The constituent buffers of an allocation `a` (p. 202): internal buffers `i` with
`Σ_j a_j B_ji > 0`. -/
def constituentBuffers {I J K : ℕ} (N : Network I J K)
    (a : Fin J → ℝ) : Set (Fin I) :=
  {i | 0 < ∑ j, a j * N.B j i.succ}

/-- Assumption 1 (EAA), p. 202: for every `z ∈ ℝ^I_+` some extreme allocation maximizes
`p(·, z)` over `ℰ` (the maximum is attained by it) and every constituent buffer of it has a
positive level. -/
def EAA {I J K : ℕ} (N : Network I J K) : Prop :=
  ∀ z : Fin I → ℝ, (∀ i, 0 ≤ z i) →
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ i ∈ constituentBuffers N a, 0 < z i

/-- Strict Leontief network (§6.1, p. 204): every service activity has exactly one buffer
in its constituency. -/
def IsStrictLeontief {I J K : ℕ} (N : Network I J K) : Prop :=
  ∀ j, IsServiceActivity N j → ∃! i : Fin (I + 1), N.B j i = 1

/-- The set `𝒥₀` of the proof of Theorem 6 (p. 204): service activities `j` whose buffer
`i(j)` has level `z_{i(j)} = 0`. The buffer `i(j)` is written relationally as the internal
buffer `i` with `B_{j i} = 1`. -/
def J0 {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ) : Set (Fin J) :=
  {j | IsServiceActivity N j ∧ ∃ i : Fin I, N.B j i.succ = 1 ∧ z i = 0}

/-- The truncated allocation `ã` of the proof of Theorem 6 (p. 204):
`ã_j = 0` for `j ∈ 𝒥₀` and `ã_j = a_j` otherwise. -/
noncomputable def truncate {I J K : ℕ} (N : Network I J K) (z : Fin I → ℝ)
    (a : Fin J → ℝ) : Fin J → ℝ :=
  Set.indicator (J0 N z)ᶜ a

end MaxPressure.StrictLeontief
