import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_DualObjective

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.237: the dual optimal value, in
`DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- `sup(D) = sup\{g(y) : y ∈ Z^U\}`, the optimal value of the dual problem `D`. -/
noncomputable def SupD {V U : Type*} [Fintype U] (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) : EReal :=
  sSup {v : EReal | ∃ y : U → ℤ, v = DualObjective F y}

end DiscreteConvex.ConjugacyDuality.Lagrange
