import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- §4.2, proof of Theorem 4.1 (p. 105), last display, "implied by Corollary 5.2":
`(1 − α)f(v, x₀) + α min_{x_δ∈Δ} f(v, x₀ + x_δ) = inf_{μ∈𝒫̂′} ∫ f(v, x) dμ(x)`,
with `𝒫̂′ = {μ ∈ 𝒫 | μ({x₀}) ≥ 1 − α, μ(x₀ + Δ) = 1}`. -/
theorem two_scenario_value {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ) (v : V)
    (hf : Continuous (f v))
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    (1 - α) * f v x₀ + α * (⨅ x : Δ, f v (x₀ + x)) = drspValue (f v) x₀ Δ (1 - α) := by sorry

end DistInterpRO.Shrinkage
