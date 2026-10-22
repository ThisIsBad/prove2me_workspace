import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting

namespace RobinsonSR.IFT

/-- Proof of Theorem 2.1, p. 46: with `Φ_p(x) := V ∩ L⁻¹[r(p, x)]`, realised as `s (r(p, x))`
where `s` is the single-valued localisation of `L⁻¹` given by strong regularity,
`x ∈ V_ε` is a fixed point of `Φ_p` iff `x ∈ V_ε` solves `0 ∈ f(p, x) + ∂ψ_C(x)`. -/
theorem fixedPoint_iff_solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) {P : Type*} (p0 : P) (x0 : X)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (U : Set (StrongDual ℝ X)) (V : Set X) (s : StrongDual ℝ X → X)
    (hs : ∀ y ∈ U, s y ∈ V ∧ y - (f p0 x0 + f' p0 x0 (s y - x0)) ∈ normalCone C (s y) ∧
      ∀ z ∈ V, y - (f p0 x0 + f' p0 x0 (z - x0)) ∈ normalCone C z → z = s y)
    (rho : ℝ) (hball : Metric.closedBall x0 rho ⊆ V) (p : P)
    (hU : ∀ x ∈ Metric.closedBall x0 rho, residual f f' p0 x0 p x ∈ U) :
    ∀ x ∈ Metric.closedBall x0 rho,
      (s (residual f f' p0 x0 p x) = x ↔ -(f p x) ∈ normalCone C x) := by sorry

end RobinsonSR.IFT

