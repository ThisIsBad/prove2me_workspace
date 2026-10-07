import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- (86), p. 874: negative moments of an a.s. positive random variable `X` through its
Laplace transform, `E[X^{-p}] = (1/Γ(p)) ∫_0^∞ t^{p-1} E[e^{-tX}] dt` for `p > 0`, stated in
`[0, ∞]` (both sides may be `+∞`). -/
theorem eq_86 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hXm : AEMeasurable X P) (hX : ∀ᵐ ω ∂P, 0 < X ω) (p : ℝ) (hp : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ (-p)) ∂P =
      ENNReal.ofReal (1 / Real.Gamma p) *
        ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 1) * ∫ ω, Real.exp (-t * X ω) ∂P) := by sorry

end PoissonDirichlet.Moments

