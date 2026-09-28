import Mathlib

open MeasureTheory

namespace DistInterpRO.Shrinkage

/-- The two-scenario distribution set of §4.2 (Xu–Caramanis–Mannor 2012, p. 104), with the
nominal mass `p` as a parameter:
`{μ ∈ 𝒫 | μ({x₀}) ≥ p, μ(x₀ + Δ) = 1}`, where `𝒫` is the set of Borel probability measures
on `ℝᵐ = EuclideanSpace ℝ (Fin m)` and `x₀ + Δ = {x₀ + x | x ∈ Δ}`.
The paper's `𝒫̂′` (Theorem 4.1) is `scenarioSet x₀ Δ (1 - α)`, and its `𝒫̂″` (Corollary 4.3)
is `scenarioSet x₀ Δ (max 0 (1 - α - α * D ^ 2 * h))`. -/
def scenarioSet {m : ℕ} (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m)))
    (p : ℝ) : Set (Measure (EuclideanSpace ℝ (Fin m))) :=
  {μ | IsProbabilityMeasure μ ∧ ENNReal.ofReal p ≤ μ {x₀} ∧
    μ ((fun x => x₀ + x) '' Δ) = 1}

/-- The value of the distributionally robust problem over `scenarioSet x₀ Δ p`:
`inf_{μ ∈ scenarioSet x₀ Δ p} ∫ F dμ`, an infimum in `ℝ` over the subtype of the set
(Bochner integrals). It is a genuine infimum when the set is nonempty and `F` is continuous
and `Δ` is compact (then `F` is bounded on `x₀ + Δ`, which carries every member). -/
noncomputable def drspValue {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (p : ℝ) : ℝ :=
  ⨅ μ : scenarioSet x₀ Δ p, ∫ x, F x ∂(μ : Measure (EuclideanSpace ℝ (Fin m)))

/-- The radius `D = max_{x ∈ Δ} ‖x‖₂` of the deviation set (Theorem 4.1, p. 104), written as
`sSup {‖x‖ | x ∈ Δ}`; for compact nonempty `Δ` the supremum is attained. -/
noncomputable def devRadius {m : ℕ} (Δ : Set (EuclideanSpace ℝ (Fin m))) : ℝ :=
  sSup ((fun x => ‖x‖) '' Δ)

/-- "`F` is twice differentiable with Hessian bounded by `h`" (Theorem 4.1, p. 104):
`F` and its derivative `DF` are (Fréchet) differentiable everywhere, and the Hessian quadratic
form satisfies `|D²F(x)[y, y]| ≤ h ‖y‖²` for all `x, y`, i.e. `−hI ⪯ H(x) ⪯ hI`. -/
def HasBoundedHessian {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → ℝ) (h : ℝ) : Prop :=
  Differentiable ℝ F ∧ Differentiable ℝ (fderiv ℝ F) ∧
    ∀ x y : EuclideanSpace ℝ (Fin m), |fderiv ℝ (fderiv ℝ F) x y y| ≤ h * ‖y‖ ^ 2

end DistInterpRO.Shrinkage
