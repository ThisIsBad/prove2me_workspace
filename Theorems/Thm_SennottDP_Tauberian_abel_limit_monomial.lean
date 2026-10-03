import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), pp. 284–285, Eqs. (A.35)–(A.36) for `f(x) = x^k`: if `u_n ∈ [0, ∞]`,
`u_0 < ∞`, and `lim_{α→1⁻} (1−α)U(α) = L < ∞`, then
`lim_{α→1⁻} (1−α) ∑ α^n u_n (α^n)^k = L ∫_0^1 x^k dx = L/(k+1)`. -/
theorem abel_limit_monomial (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (k : ℕ) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ((α : ℝ≥0∞) ^ n) ^ k)
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L / ((k : ℝ≥0∞) + 1))) := by sorry

end SennottDP.Tauberian
