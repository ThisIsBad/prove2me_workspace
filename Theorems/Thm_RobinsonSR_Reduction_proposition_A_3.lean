import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace

namespace RobinsonSR.Reduction

/-- Proposition A.3 (Robinson 1980, p. 58). Let `C` be a nonempty polyhedral convex set in `ℝⁿ`,
`y₀ ∈ ℝⁿ`, `F := ∂ψ*_C(-y₀)`, `x₀ ∈ F`, `T := T_F(x₀)` and `L` the subspace parallel to `F`.
Then there are neighbourhoods `U` and `V` of the origin such that for each `h ∈ U` and `k ∈ V`,
`0 ∈ (y₀ + k) + ∂ψ_C(x₀ + h)` if and only if `0 ∈ P_L k + ∂ψ_T(h)`, where `P_L` is the
orthogonal projector on `L`. -/
theorem proposition_A_3 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (y0 x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ exposedFace C y0) :
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∃ V ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ∀ h ∈ U, ∀ k ∈ V,
        (-(y0 + k) ∈ normalCone C (x0 + h) ↔ -(L.starProjection k) ∈ normalCone T h) := by sorry

end RobinsonSR.Reduction

