import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDuality_FromEReal

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.212, Eq. (8.11)_Z: the discrete (integer)
Legendre-Fenchel transform, in `DiscreteConvex.ConjugacyDuality`.
-/

namespace DiscreteConvex.ConjugacyDuality

/-- The discrete Legendre-Fenchel transform `f•(p) = sup\{⟨p,x⟩ - f(x) : x ∈ Zⱽ\}` for
`p ∈ Zⱽ` (Eq. (8.11) restricted to integer `p`, i.e. `(8.11)_Z`). The defining supremum is
taken in `EReal` (a complete lattice) and then projected back to `WithTop ℝ` via `FromEReal`,
so `f•` has the same type as `f` itself. -/
noncomputable def ConvexConjugate {V : Type*} [Fintype V] (f : (V → ℤ) → WithTop ℝ)
    (p : V → ℤ) : WithTop ℝ :=
  FromEReal (sSup {v : EReal | ∃ x : V → ℤ,
    v = ((∑ i, (p i : ℝ) * (x i : ℝ) : ℝ) : EReal) - ToEReal (f x)})

end DiscreteConvex.ConjugacyDuality
