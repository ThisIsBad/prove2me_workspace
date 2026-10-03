import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.236, Eq. (8.58): the Lagrangian kernel of a
perturbation function, in `DiscreteConvex.ConjugacyDuality.Lagrange`.
-/

open DiscreteConvex.ConjugacyDuality

namespace DiscreteConvex.ConjugacyDuality.Lagrange

/-- The **Lagrangian function** `K(x,y) = inf\{F(x,u) + ⟨u,y⟩ : u ∈ Z^U\}` (Eq. (8.58))
associated with a perturbation `F : Zⱽ × Z^U → Z ∪ {+∞}` of a primal problem. Landing in
`EReal` since the infimum need not be finite. -/
noncomputable def LagrangianKernel {V U : Type*} [Fintype U]
    (F : (V → ℤ) → (U → ℤ) → WithTop ℝ) (x : V → ℤ) (y : U → ℤ) : EReal :=
  sInf {v : EReal | ∃ u : U → ℤ,
    v = ToEReal (F x u) + ((∑ i, (u i : ℝ) * (y i : ℝ) : ℝ) : EReal)}

end DiscreteConvex.ConjugacyDuality.Lagrange
