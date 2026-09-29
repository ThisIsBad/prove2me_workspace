import Mathlib

namespace SatiaLave.MaxMin

open Finset

/-- A finite-state, discrete-time, discounted Markovian decision process whose transition
probabilities are uncertain (Satia–Lave 1973, pp. 728–729). States are the elements of the
finite type `S` (the paper's `1, …, N`); in state `i` the decisions are the elements of the
finite type `D i` (the paper's `1, …, K_i`). `r i k j` is the reward `r^k_ij` of a transition
`i → j` under decision `k`, `β` the discount factor, and `U i k` the set `S_i^k` of admissible
probability rows `p_i^k`. -/
structure UncertainMDP (S : Type*) [Fintype S] (D : S → Type*) where
  /-- the reward `r^k_ij` -/
  r : (i : S) → D i → S → ℝ
  /-- the discount factor `β` -/
  β : ℝ
  β_nonneg : 0 ≤ β
  β_lt_one : β < 1
  /-- the uncertainty set `S_i^k` of probability rows -/
  U : (i : S) → D i → Set (S → ℝ)
  /-- every admissible row is a probability row -/
  U_subset : ∀ i k, U i k ⊆ stdSimplex ℝ S
  /-- "`S_i^k` is a closed convex set for all `i` and all `k`" -/
  U_closed : ∀ i k, IsClosed (U i k)
  U_convex : ∀ i k, Convex ℝ (U i k)
  /-- (added) every uncertainty set contains a feasible row -/
  U_nonempty : ∀ i k, (U i k).Nonempty

variable {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}

/-- A pure stationary policy `A = (A_1, …, A_N)`: one decision in each state. -/
abbrev Policy (S : Type*) (D : S → Type*) := (i : S) → D i

/-- Nature's choice `P ∈ S`: one admissible probability row `P i k ∈ S_i^k` for every state
`i` and every decision `k`. -/
def Sel (M : UncertainMDP S D) : Type _ :=
  {P : (i : S) → D i → S → ℝ // ∀ i k, P i k ∈ M.U i k}

/-- The transition matrix `P^A = (p^A_ij)` of policy `A` under nature's choice `P`. -/
def transMat (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) : Matrix S S ℝ :=
  Matrix.of fun i j => P.1 i (A i) j

/-- The one-step expected reward `Σ_j p^A_ij r^A_ij` of policy `A` under `P`. -/
def rewardVec (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) : S → ℝ :=
  fun i => ∑ j, P.1 i (A i) j * M.r i (A i) j

/-- `v` solves the present-value equations (5) for policy `A` under `P`:
`v_i = Σ_j p^A_ij (r^A_ij + β v_j)` for every state `i`. -/
def SolvesEq5 (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (v : S → ℝ) : Prop :=
  ∀ i, v i = ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * v j)

/-- The present-value vector `v^A = [I − βP^A]⁻¹ (Σ_j p^A_ij r^A_ij)_i` of policy `A` under
nature's choice `P`. -/
noncomputable def presentValue (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) : S → ℝ :=
  Matrix.mulVec (1 - M.β • transMat M A P)⁻¹ (rewardVec M A P)

/-- Nature's minimum for policy `A` in state `i`: the infimum, over all admissible choices
`P ∈ S`, of the present value of `A` in state `i`. -/
noncomputable def robustValue (M : UncertainMDP S D) (A : Policy S D) (i : S) : ℝ :=
  ⨅ P : Sel M, presentValue M A P i

variable [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]

/-- The max-min return of criterion (2) in state `i`: the maximum over all pure stationary
policies of nature's minimum. -/
noncomputable def maxMinValue (M : UncertainMDP S D) (i : S) : ℝ :=
  (Finset.univ : Finset (Policy S D)).sup' Finset.univ_nonempty (fun A => robustValue M A i)

/-- `A` is max-min optimal: its max-min return equals the optimal max-min return in every
state. -/
def IsMaxMinOptimal (M : UncertainMDP S D) (A : Policy S D) : Prop :=
  ∀ i, robustValue M A i = maxMinValue M i

/-- `A` is `ε`-optimal (p. 731): its returns are within `±ε` of the optimal returns. -/
def IsEpsMaxMinOptimal (M : UncertainMDP S D) (ε : ℝ) (A : Policy S D) : Prop :=
  ∀ i, |robustValue M A i - maxMinValue M i| ≤ ε

end SatiaLave.MaxMin
