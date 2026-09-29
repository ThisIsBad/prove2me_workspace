import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

/-- Theorem 4.1 (Xu–Caramanis–Mannor 2012, p. 104). If there is `h ≥ 0` with
`−hI ⪯ H_v(x) ⪯ hI` for all `v, x`, then for all `v` the minimum over `αΔ` is attained and
`inf_{μ∈𝒫̂′} ∫ f(v, x) dμ(x) − αD²h ≤ min_{x_δ∈αΔ} f(v, x₀ + x_δ)
  ≤ inf_{μ∈𝒫̂′} ∫ f(v, x) dμ(x) + αD²h`,
with `D = max_{x∈Δ} ‖x‖₂` and `𝒫̂′ = {μ ∈ 𝒫 | μ({x₀}) ≥ 1 − α, μ(x₀ + Δ) = 1}`.
Added standing hypotheses (implicit on the page): `Δ` compact and `0 ∈ Δ`. -/
theorem theorem_4_1 {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ℝ) (hh : 0 ≤ h) (hf : ∀ v, HasBoundedHessian (f v) h) :
    ∀ v : V,
      (∃ x ∈ α • Δ, ∀ y ∈ α • Δ, f v (x₀ + x) ≤ f v (x₀ + y)) ∧
      drspValue (f v) x₀ Δ (1 - α) - α * devRadius Δ ^ 2 * h ≤
        (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ∧
      (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ≤
        drspValue (f v) x₀ Δ (1 - α) + α * devRadius Δ ^ 2 * h := by sorry

end DistInterpRO.Shrinkage
