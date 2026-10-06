import Mathlib

namespace DiscreteConvex.CombinatorialC

/-- `g` is supermodular on `S`: supermodularity asked only of the arguments in `S`. Murota,
*Discrete Convex Analysis*, SIAM 2003, p. 74 defines `F(w,c)` for `c ≥ 0` only, so the `c` part
of Theorem 2.22 is a statement on the nonnegative orthant. -/
def SupermodularOn {W : Type*} [Fintype W] (S : Set (W → ℝ)) (g : (W → ℝ) → ℝ) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, g p + g q ≤ g (p ⊔ q) + g (p ⊓ q)

end DiscreteConvex.CombinatorialC
