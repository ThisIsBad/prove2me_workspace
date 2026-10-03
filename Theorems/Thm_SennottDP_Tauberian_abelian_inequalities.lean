import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 282, Theorem A.4.2, inequalities (A.28): for nonnegative terms
`u_n ∈ [0, ∞]` with `u_0 < ∞` and `w_n = ∑_{k<n} u_k`,
`lim inf_n w_n/n ≤ lim inf_{α→1⁻} (1−α)U(α) ≤ lim sup_{α→1⁻} (1−α)U(α) ≤ lim sup_n w_n/n`,
all four quantities taken in `[0, ∞]`. -/
theorem abelian_inequalities (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) :
    liminf (cesaroMean u) atTop ≤ liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      liminf (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ∧
      limsup (abelMean u) (𝓝[<] (1 : ℝ≥0)) ≤ limsup (cesaroMean u) atTop := by sorry

end SennottDP.Tauberian
