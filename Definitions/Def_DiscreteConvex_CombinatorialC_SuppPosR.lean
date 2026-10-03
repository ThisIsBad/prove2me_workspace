import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, Eq. (2.21): the positive support of a real
vector, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- The positive support `supp⁺(x) = \{i | x_i > 0\}` (Eq. (2.21)), as a `Finset`. -/
noncomputable def SuppPosR {W : Type*} [Fintype W] [DecidableEq W] (x : W → ℝ) : Finset W :=
  Finset.univ.filter (fun i => 0 < x i)

end DiscreteConvex.CombinatorialC
