import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

/-- Lemma A.5 (p. 15), with the sign misprint corrected: if `X ≻ 0` solves
`AᵀX + XA + Q = 0` (the paper prints `− Q`) with `A` Hurwitz and `Q ≻ 0`, then
`λₙ(X) ≥ λ₁(Q) / (2σ(A))` and `λ₁(X) ≥ λ₁(Q) / (2‖A‖)`, `σ(A) = −maxᵢ ℜλᵢ(A)`. -/
theorem lyapunov_eigen_lower_bounds {n : ℕ} (A X Q : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsHurwitz A) (hQ : Q.PosDef) (hX : X.PosDef)
    (hLyap : A.transpose * X + X * A + Q = 0) :
    lamMin Q / (2 * stabDegree A) ≤ lamMax X ∧
      lamMin Q / (2 * specNorm A) ≤ lamMin X := by sorry

end FatkhullinPolyak.Discrete
