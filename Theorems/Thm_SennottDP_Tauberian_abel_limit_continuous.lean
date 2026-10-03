import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 285, Eq. (A.35) for continuous functions: if `u_n ∈ [0, ∞]`, `u_0 < ∞`, and
`lim_{α→1⁻} (1−α)U(α) = L < ∞`, then for every real function `f` continuous on `[0, 1]`,
`lim_{α→1⁻} (1−α) U_f(α) = L ∫_0^1 f(x) dx`, where `U_f(α) = ∑ α^n u_n f(α^n)` (A.34).
(Under the hypothesis every `u_n` is finite, so `U_f` is a real series.) -/
theorem abel_limit_continuous (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ)) * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * f ((α : ℝ) ^ n))
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L.toReal * ∫ x in (0 : ℝ)..1, f x)) := by sorry

end SennottDP.Tauberian
