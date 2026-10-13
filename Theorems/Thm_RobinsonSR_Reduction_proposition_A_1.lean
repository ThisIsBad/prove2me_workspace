import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting

open scoped Topology RealInnerProductSpace

namespace RobinsonSR.Reduction

/-- Proposition A.1 (Robinson 1980, p. 58). Let `C` be a nonempty polyhedral convex set in `ℝⁿ`
and `x₀ ∈ C`. Then there is a neighbourhood `U` of the origin with
`(C - x₀) ∩ U = T_C(x₀) ∩ U`, where `T_C(x₀) = ∂ψ_C(x₀)°`. -/
theorem proposition_A_1 {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hCp : IsPolyhedral C)
    (hCne : C.Nonempty) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ C) :
    ∃ U ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      ((fun c => c - x0) '' C) ∩ U = tangentCone C x0 ∩ U := by sorry

end RobinsonSR.Reduction

