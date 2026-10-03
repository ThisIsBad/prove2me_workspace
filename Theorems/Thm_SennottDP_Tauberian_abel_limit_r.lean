import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_KaramataR

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 285, Eq. (A.35) for `f = r` (Fig. A.1): if `u_n ∈ [0, ∞]`, `u_0 < ∞`, and
`lim_{α→1⁻} (1−α)U(α) = L < ∞`, then `lim_{α→1⁻} (1−α) ∑ α^n u_n r(α^n) = L ∫_0^1 r(x) dx`. -/
theorem abel_limit_r (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ENNReal.ofReal (r ((α : ℝ) ^ n)))
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L * ENNReal.ofReal (∫ x in (0 : ℝ)..1, r x))) := by sorry

end SennottDP.Tauberian
