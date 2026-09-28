import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_Matrix

namespace FatkhullinPolyak.Discrete

/-- Lemma A.1 (p. 15): for Hurwitz `A`, solutions `X`, `Y` of the dual Lyapunov equations
`AᵀX + XA + W = 0` and `AY + YAᵀ + V = 0` satisfy `Tr(XV) = Tr(YW)`. -/
theorem trace_duality_lyapunov {n : ℕ} (A X Y W V : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsHurwitz A)
    (hX : A.transpose * X + X * A + W = 0)
    (hY : A * Y + Y * A.transpose + V = 0) :
    Matrix.trace (X * V) = Matrix.trace (Y * W) := by sorry

end FatkhullinPolyak.Discrete
