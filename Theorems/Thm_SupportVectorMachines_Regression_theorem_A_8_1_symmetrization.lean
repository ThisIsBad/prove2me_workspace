import Mathlib
import Definitions.Def_SupportVectorMachines_Regression_IsRademacherSequence

open MeasureTheory ProbabilityTheory TopologicalSpace

namespace SupportVectorMachines.Regression

/-- Theorem A.8.1 (Symmetrization), p. 535: let `Ψ : [0,∞) → [0,∞)` be convex and non-decreasing,
`E` a separable Banach space, `(Ω,A,P)` a probability space, `ξ₁,…,ξₙ : Ω → E` i.i.d.
`P`-integrable random variables, and `ε₁,…,εₙ` a Rademacher sequence with respect to some `ν`.
Then `E_P Ψ(‖(1/n) ∑ᵢ(ξᵢ - E_P ξᵢ)‖) ≤ E_P E_ν Ψ(2‖(1/n) ∑ᵢ εᵢξᵢ‖)`. The book's `Ψ : [0,∞) → [0,∞)`
codomain restriction (nonnegativity) is what lets both expectations be always-defined, possibly
infinite, quantities with no integrability hypothesis anywhere in the statement; rendered here as
`ℝ≥0∞`-valued `lintegral`s composing `Ψ` through `ENNReal.ofReal`, with an explicit `hΨnn`/`hΨmeas`
in place of the book's `[0,∞) → [0,∞)` codomain, rather than as real-valued Bochner integrals
(which would silently return the junk value `0` on a non-integrable `Ψ`-composed integrand — no
such integrability is assumed or available here, since `Ψ` need only be convex and non-decreasing,
hence of arbitrary growth). -/
theorem theorem_A_8_1_symmetrization
    (Ψ : ℝ → ℝ) (hΨconv : ConvexOn ℝ (Set.Ici 0) Ψ) (hΨmono : MonotoneOn Ψ (Set.Ici 0))
    (hΨnn : ∀ x ∈ Set.Ici (0 : ℝ), 0 ≤ Ψ x) (hΨmeas : Measurable Ψ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SeparableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (ξ : Fin n → Ω → E) (hξmeas : ∀ i, Measurable (ξ i))
    (hξindep : iIndepFun ξ P) (hξident : ∀ i j, IdentDistrib (ξ i) (ξ j) P P)
    (hξint : ∀ i, Integrable (ξ i) P)
    {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsProbabilityMeasure ν]
    (ε : Fin n → Θ → ℝ) (hε : IsRademacherSequence ε ν) :
    ∫⁻ ω, ENNReal.ofReal (Ψ ‖(n : ℝ)⁻¹ • ∑ i, (ξ i ω - ∫ ω', ξ i ω' ∂P)‖) ∂P ≤
      ∫⁻ ω, ∫⁻ θ, ENNReal.ofReal (Ψ (2 * ‖(n : ℝ)⁻¹ • ∑ i, ε i θ • ξ i ω‖)) ∂ν ∂P := by sorry

end SupportVectorMachines.Regression
