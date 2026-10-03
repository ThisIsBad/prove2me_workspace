import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_DualObjective
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_SupD

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.237: the dual optimal solution set, in
`DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- `opt(D) = \{y ∈ Z^U : g(y) = sup(D)\}`, the optimal solution set of the dual problem. -/
noncomputable def OptD {V U : Type*} [Fintype U] (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) :
    Set (U → ℤ) :=
  {y | DualObjective F y = SupD F}

end DiscreteConvex.ConjugacyDuality.Lagrange
