import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace

namespace RobinsonSR.Reduction

/-- Proposition A.2 (Robinson 1980, p. 58). Let `C` be a nonempty polyhedral convex set in `ℝⁿ`,
`y₀ ∈ ℝⁿ` and `F := ∂ψ*_C(-y₀)`. Then for each `x ∈ F`,
`∂ψ_F(x) = ∂ψ_C(x) + y₀ℝ₊ = {y + α y₀ | y ∈ ∂ψ_C(x), α ≥ 0}`; and for each `y` near `y₀`,
`∂ψ*_C(-y) ⊂ F`. -/
theorem proposition_A_2 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (y0 : EuclideanSpace ℝ (Fin n)) :
    (∀ x ∈ exposedFace C y0, normalCone (exposedFace C y0) x =
        {v | ∃ y ∈ normalCone C x, ∃ α : ℝ, 0 ≤ α ∧ v = y + α • y0}) ∧
    ∀ᶠ y in 𝓝 y0, exposedFace C y ⊆ exposedFace C y0 := by sorry

end RobinsonSR.Reduction

