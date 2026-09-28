import Mathlib

namespace HeldWolfeCrowder.CoreProblem

open scoped InnerProductSpace
open Filter Topology

/-- **Eq. (2.2), p. 64.** The piecewise-linear concave function
`w(π) = min { c_k + π·v_k : k = 1, …, K }` on `Eⁿ = EuclideanSpace ℝ (Fin n)`, for data
`c : ι → ℝ`, `v : ι → Eⁿ` indexed by a finite nonempty type `ι` (the paper's `{1, …, K}`). -/
noncomputable def w {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (π : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun k => c k + ⟪π, v k⟫_ℝ)

/-- **Eq. (2.3), p. 64.** The index `k` attains the minimum in (2.2) at `π`, i.e.
`c_k + π·v_k = w(π)`, i.e. `v_k ∈ V(π)`. -/
def IsMinIndex {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (π : EuclideanSpace ℝ (Fin n)) (k : ι) :
    Prop :=
  c k + ⟪π, v k⟫_ℝ = w c v π

/-- **The subgradient algorithm (2.5)–(2.6), p. 66.** A run of the method: positive step sizes
`t_j`, an index `k(j)` chosen at step `j` that attains the minimum (2.2) at `π^j`
(so `v(π^j) = v_{k(j)} ∈ V(π^j)`, (2.5)), and the update `π^{j+1} = π^j + t_j v(π^j)`
for `j = 0, 1, …` (2.6). The starting point `π^0 = π 0` is arbitrary. -/
structure IsSubgradientRun {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (t : ℕ → ℝ)
    (π : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι) : Prop where
  /-- The step sizes are positive scalars. -/
  step_pos : ∀ j, 0 < t j
  /-- `k(j)` attains the minimum in (2.2) at `π^j`. -/
  index_min : ∀ j, IsMinIndex c v (π j) (k j)
  /-- The update (2.6). -/
  step : ∀ j, π (j + 1) = π j + t j • v (k j)

/-- **Step-size conditions (2.7), p. 67.** `t_j → 0` and `Σ_{j=0}^∞ t_j = ∞`, the latter stated
as: the partial sums `Σ_{j<N} t_j` tend to `+∞`. -/
def StepSizeCond (t : ℕ → ℝ) : Prop :=
  Tendsto t atTop (𝓝 0) ∧
    Tendsto (fun N => ∑ j ∈ Finset.range N, t j) atTop atTop

/-- **The dual linear program (6.1), p. 81: feasibility.** `y_k ≥ 0` for all `k`,
`Σ_k y_k = 1` and `Σ_k −v_k y_k = 0` (written here as `Σ_k y_k v_k = 0`). -/
def DualFeasible {n : ℕ} {ι : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin n)) (y : ι → ℝ) : Prop :=
  (∀ k, 0 ≤ y k) ∧ ∑ k, y k = 1 ∧ ∑ k, y k • v k = 0

/-- **(6.1): objective** `Σ_k c_k y_k`. -/
def dualObj {ι : Type*} [Fintype ι] (c : ι → ℝ) (y : ι → ℝ) : ℝ :=
  ∑ k, c k * y k

/-- **(6.1): optimality.** `y` is feasible for (6.1) and minimizes `Σ_k c_k y_k` over all
feasible points, i.e. `y` solves (6.1). -/
def IsDualOptimal {n : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (y : ι → ℝ) : Prop :=
  DualFeasible v y ∧ ∀ y' : ι → ℝ, DualFeasible v y' → dualObj c y ≤ dualObj c y'

/-- **The core problem `P(J, J*)`, p. 81: feasibility.** The variables `y_j` are indexed by the
iterations `j ∈ [J, J*]` (values of `y` outside `[J, J*]` play no role); with
`v^j = v_{k(j)}`, the constraints are `y_j ≥ 0` for `J ≤ j ≤ J*`, `Σ_{j=J}^{J*} y_j = 1` and
`Σ_{j=J}^{J*} −v^j y_j = 0` (written here as `Σ_{j=J}^{J*} y_j v^j = 0`). Repeated indices
`k(j)` give repeated columns; nothing is deduplicated. -/
def CoreFeasible {n : ℕ} {ι : Type*}
    (v : ι → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι) (J Jstar : ℕ) (y : ℕ → ℝ) : Prop :=
  (∀ j ∈ Finset.Icc J Jstar, 0 ≤ y j) ∧
    ∑ j ∈ Finset.Icc J Jstar, y j = 1 ∧
    ∑ j ∈ Finset.Icc J Jstar, y j • v (k j) = 0

/-- **`P(J, J*)`: objective** `Σ_{j=J}^{J*} c^j y_j` with `c^j = c_{k(j)}`. -/
def coreObj {ι : Type*} (c : ι → ℝ) (k : ℕ → ι) (J Jstar : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc J Jstar, c (k j) * y j

/-- **`P(J, J*)`: optimality.** `y` is feasible for `P(J, J*)` and minimizes its objective over
all feasible points, i.e. `y` is a solution of `P(J, J*)`. -/
def IsCoreOptimal {n : ℕ} {ι : Type*}
    (c : ι → ℝ) (v : ι → EuclideanSpace ℝ (Fin n)) (k : ℕ → ι) (J Jstar : ℕ) (y : ℕ → ℝ) :
    Prop :=
  CoreFeasible v k J Jstar y ∧
    ∀ y' : ℕ → ℝ, CoreFeasible v k J Jstar y' → coreObj c k J Jstar y ≤ coreObj c k J Jstar y'

open Classical in
/-- **Aggregation of a point of `P(J, J*)` to a point of (6.1).** The weight of index `i` is the
total weight of the iterations `j ∈ [J, J*]` at which `i` was chosen:
`y_i = Σ { y_j : J ≤ j ≤ J*, k(j) = i }`. This map carries feasible points of `P(J, J*)` to
feasible points of (6.1) with the same objective value; it is how "a solution of `P(J, J*)`
solves (6.1)" is read. -/
noncomputable def aggregate {ι : Type*} (k : ℕ → ι) (J Jstar : ℕ) (y : ℕ → ℝ) : ι → ℝ :=
  fun i => ∑ j ∈ (Finset.Icc J Jstar).filter (fun j => k j = i), y j

end HeldWolfeCrowder.CoreProblem
