import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_PrimalValue
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_InfP

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.237: the primal optimal solution set, in
`DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

open DiscreteConvex.ConjugacyDuality

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- `opt(P) = \{x ∈ Zⱽ : f(x) = inf(P)\}`, the optimal solution set of the primal problem. -/
noncomputable def OptP {V U : Type*} [Fintype U] [Zero (U → ℤ)]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) : Set (V → ℤ) :=
  {x | ToEReal (PrimalValue F x) = InfP F}

end DiscreteConvex.ConjugacyDuality.Lagrange
