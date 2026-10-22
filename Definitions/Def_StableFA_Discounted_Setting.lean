import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace StableFA.Discounted

open Filter Topology

/-- An averager (Gordon 1995, p. 7), indexed by the `n` states of a finite MDP: for each
state `i` there is a constant `k i`, a nonnegative weight `βc i` on that constant (the
paper's `β_i`) and nonnegative weights `β i j` (the paper's `β_ij`) on the target values,
with `βc i + ∑ j, β i j = 1`. The weights are fixed data and do not depend on the targets. -/
structure Averager (n : ℕ) where
  /-- the predetermined constants `k_i` -/
  k : Fin n → ℝ
  /-- the weight `β_i` on the constant `k_i` -/
  βc : Fin n → ℝ
  /-- the weight `β_ij` of target value `Y_j` in fitted value `Ŷ_i` -/
  β : Fin n → Fin n → ℝ
  βc_nonneg : ∀ i, 0 ≤ βc i
  β_nonneg : ∀ i j, 0 ≤ β i j
  sum_eq_one : ∀ i, βc i + ∑ j, β i j = 1

/-- The mapping `M_A` associated with the averager `A` (pp. 5 and 7): it sends a vector of
target values `Y` to the vector of fitted values `Ŷ_i = β_i k_i + ∑_j β_ij Y_j`. -/
def Averager.apply {n : ℕ} (A : Averager n) (Y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => A.βc i * A.k i + ∑ j, A.β i j * Y j

/-- Two operators `M_F` and `T` on `ℝ^n` are compatible (p. 5) if repeated application of
`M_F ∘ T` converges to some point from every initial guess `x₀`. -/
def Compatible {n : ℕ} (MF T : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ x₀ : Fin n → ℝ, ∃ x : Fin n → ℝ, Tendsto (fun k => (MF ∘ T)^[k] x₀) atTop (𝓝 x)

end StableFA.Discounted
