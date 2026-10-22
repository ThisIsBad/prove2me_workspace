import Mathlib
import Definitions.Def_RobinsonSR_IFT_Setting

namespace RobinsonSR.IFT

open scoped Topology

/-- Robinson 1980, Theorem 2.1 (p. 45): implicit-function theorem for strongly regular
generalized equations `0 ∈ f(p, x) + ∂ψ_C(x)`. -/
theorem theorem_2_1 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C : Set X) (hC : IsClosed C) (hCc : Convex ℝ C)
    (Ω : Set X) (hΩ : IsOpen Ω) (x0 : X) (hx0 : x0 ∈ Ω)
    {P : Type*} [TopologicalSpace P] (p0 : P)
    (f : P → X → StrongDual ℝ X) (f' : P → X → (X →L[ℝ] StrongDual ℝ X))
    (hf' : ∀ p, ∀ x ∈ Ω, HasFDerivAt (f p) (f' p x) x)
    (hfc : ContinuousAt (fun z : P × X => f z.1 z.2) (p0, x0))
    (hf'c : ContinuousAt (fun z : P × X => f' z.1 z.2) (p0, x0))
    (hsol : -(f p0 x0) ∈ normalCone C x0)
    (lam : ℝ) (hreg : StronglyRegular C (f p0 x0) (f' p0 x0) x0 lam) :
    ∀ eps > 0, ∃ N ∈ 𝓝 p0, ∃ W ∈ 𝓝 x0, W ⊆ Ω ∧ ∃ x : P → X,
      (∀ p ∈ N, x p ∈ W ∧ -(f p (x p)) ∈ normalCone C (x p) ∧
          ∀ z ∈ W, -(f p z) ∈ normalCone C z → z = x p) ∧
      ∀ p ∈ N, ∀ q ∈ N, ‖x p - x q‖ ≤ (lam + eps) * ‖f p (x q) - f q (x q)‖ := by sorry

end RobinsonSR.IFT

