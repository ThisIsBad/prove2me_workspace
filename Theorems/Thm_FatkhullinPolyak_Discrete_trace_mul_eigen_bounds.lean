import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

/-- Lemma A.4 (p. 15): for positive semidefinite `A`, `B`,
`λ₁(A) Tr(B) ≤ Tr(AB) ≤ λₙ(A) Tr(B)`. -/
theorem trace_mul_eigen_bounds {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    lamMin A * Matrix.trace B ≤ Matrix.trace (A * B) ∧
      Matrix.trace (A * B) ≤ lamMax A * Matrix.trace B := by sorry

end FatkhullinPolyak.Discrete
