import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDuality_Lagrange_PrimalValue

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.237: the primal optimal value, in
`DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

open DiscreteConvex.ConjugacyDuality

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- `inf(P) = inf\{f(x) : x ∈ Zⱽ\}`, the optimal value of the primal problem `P`. -/
noncomputable def InfP {V U : Type*} [Zero (U → ℤ)] (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) :
    EReal :=
  sInf {v : EReal | ∃ x : V → ℤ, v = ToEReal (PrimalValue F x)}

end DiscreteConvex.ConjugacyDuality.Lagrange
