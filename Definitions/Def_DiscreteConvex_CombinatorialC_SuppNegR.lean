import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, Eq. (2.21): the negative support of a real
vector, in `DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- The negative support `supp⁻(x) = \{i | x_i < 0\}` (Eq. (2.21)), as a `Finset`. -/
noncomputable def SuppNegR {W : Type*} [Fintype W] [DecidableEq W] (x : W → ℝ) : Finset W :=
  Finset.univ.filter (fun i => x i < 0)

end DiscreteConvex.CombinatorialC
