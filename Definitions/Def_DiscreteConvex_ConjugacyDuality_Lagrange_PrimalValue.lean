import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.236, Eq. (8.52)-(8.54): the primal objective
recovered from a perturbation function at zero perturbation, in
`DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- The **primal objective** `f(x) = F(x,0)` (Eq. (8.54)) recovered from the perturbation
`F : Zⱽ × Z^U → Z ∪ {+∞}` at the zero perturbation. -/
def PrimalValue {V U : Type*} [Zero (U → ℤ)] (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) (x : V → ℤ) :
    WithTop ℝ :=
  F x 0

end DiscreteConvex.ConjugacyDuality.Lagrange
