import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace

namespace RobinsonSR.Reduction

/-- The correspondence (A.4) (Robinson 1980, p. 60). Let `C` be a nonempty polyhedral convex set
in `ℝⁿ`, `A` an `n × n` matrix, `a ∈ ℝⁿ`, and let `x₀` solve `0 ∈ A x + a + ∂ψ_C(x)` (A.1).
With `y₀ := A x₀ + a`, `F := ∂ψ*_C(-y₀)`, `T := T_F(x₀)` and `L` the subspace parallel to `F`,
there are neighbourhoods `N` of `x₀` and `W` of `0` such that for `x ∈ N` and `y ∈ W`,
`y ∈ A x + a + ∂ψ_C(x)` (A.2) holds if and only if `0 ∈ P_L(A h - y) + ∂ψ_T(h)` with
`h := x - x₀` (A.4), written here as `P_L y - P_L (A h) ∈ ∂ψ_T(h)`. -/
theorem correspondence_A_4 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n))
    (hsol : -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0) :
    let y0 := Matrix.toEuclideanLin A x0 + a
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    ∃ N ∈ 𝓝 x0, ∃ W ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ∀ x ∈ N, ∀ y ∈ W,
      (y - (Matrix.toEuclideanLin A x + a) ∈ normalCone C x ↔
        L.starProjection y - L.starProjection (Matrix.toEuclideanLin A (x - x0)) ∈
          normalCone T (x - x0)) := by sorry

end RobinsonSR.Reduction

