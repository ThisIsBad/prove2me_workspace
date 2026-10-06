import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.83, Eq. (2.53): submodularity of a real-valued
function, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Submodularity** (2.53) of `g : Rᵂ → R`: `g(p) + g(q) ≥ g(p ∨ q) + g(p ∧ q)`. -/
def Submodular {W : Type*} [Fintype W] (g : (W → ℝ) → ℝ) : Prop :=
  ∀ p q : W → ℝ, g p + g q ≥ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.CombinatorialC
