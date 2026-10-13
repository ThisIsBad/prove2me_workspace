import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix

namespace RobinsonSR.NLP

/-- Theorem 4.1, p. 56: let `θ, g, h` be functions from an open set `Ω ⊆ ℝⁿ` to `ℝ, ℝᵖ, ℝ^q`,
differentiable on `Ω` (the standing assumption of (4.1)) and twice differentiable at `x₀ ∈ Ω`.
Suppose `(x₀, u₀, v₀)` solves (4.3). If the strong second-order sufficient condition (a′) holds
at `(x₀, u₀, v₀)` together with linear independence (b) of the gradients of the binding
constraints, then (4.3) is strongly regular there. -/
theorem theorem_4_1 {n p q : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ Ω)
    (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (hθ : DifferentiableOn ℝ θ Ω)
    (hg : ∀ i, DifferentiableOn ℝ (fun x => g x i) Ω)
    (hh : ∀ j, DifferentiableOn ℝ (fun x => h x j) Ω)
    (hθ2 : DifferentiableAt ℝ (gradient θ) x0)
    (hg2 : ∀ i, DifferentiableAt ℝ (gradient (fun x => g x i)) x0)
    (hh2 : ∀ j, DifferentiableAt ℝ (gradient (fun x => h x j)) x0)
    (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q))
    (hsol : -(kktMap θ g h (mk x0 u0 v0)) ∈ RobinsonSR.Reduction.normalCone (kktCone n p q) (mk x0 u0 v0))
    (hSSOSC : ∀ y : EuclideanSpace ℝ (Fin n), y ≠ 0 →
      (∀ i, 0 < u0 i → ⟪gradient (fun x => g x i) x0, y⟫ = 0) →
      (∀ j, ⟪gradient (fun x => h x j) x0, y⟫ = 0) →
      0 < ⟪y, lagHess θ g h x0 u0 v0 y⟫)
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun i : {i : Fin p // g x0 i = 0} => gradient (fun x => g x i) x0)
        (fun j : Fin q => gradient (fun x => h x j) x0))) :
    StronglyRegularAt (kktMap θ g h) (kktCone n p q) (mk x0 u0 v0) := by sorry

end RobinsonSR.NLP

