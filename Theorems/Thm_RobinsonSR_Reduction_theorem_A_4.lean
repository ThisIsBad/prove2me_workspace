import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace

namespace RobinsonSR.Reduction

/-- Theorem A.4 (Robinson 1980, p. 60). Let `C` be a (nonempty) polyhedral convex set in `ℝⁿ`,
`A` an `n × n` matrix and `a ∈ ℝⁿ`, and let `x₀` solve `0 ∈ A x + a + ∂ψ_C(x)` (A.1). With
`y₀ := A x₀ + a`, `F := ∂ψ*_C(-y₀)`, `T := T_F(x₀)` and `L` the subspace parallel to `F`,
(A.1) is strongly regular at `x₀` if and only if its reduced form (i) is vacuous (`L = {0}`), or
(ii) has an inverse which is single-valued on all of `L`: for every `z ∈ L` there is exactly one
`w` with `z ∈ P_L A w + ∂ψ_T(w)`. -/
theorem theorem_A_4 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (A : Matrix (Fin n) (Fin n) ℝ) (a x0 : EuclideanSpace ℝ (Fin n))
    (hsol : -(Matrix.toEuclideanLin A x0 + a) ∈ normalCone C x0) :
    let y0 := Matrix.toEuclideanLin A x0 + a
    let F := exposedFace C y0
    let T := tangentCone F x0
    let L := parallelSubspace F
    (∃ lam : ℝ, StronglyRegularLin C A a x0 lam) ↔
      (L = ⊥ ∨ ∀ z ∈ L, ∃! w : EuclideanSpace ℝ (Fin n),
        z - L.starProjection (Matrix.toEuclideanLin A w) ∈ normalCone T w) := by sorry

end RobinsonSR.Reduction

