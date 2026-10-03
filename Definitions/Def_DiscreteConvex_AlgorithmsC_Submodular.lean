import Mathlib

namespace DiscreteConvex.AlgorithmsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- A set function `ρ : 2^W → Z` is submodular, with `ρ(∅) = 0` — the standing normalization of
Murota, *Discrete Convex Analysis*, SIAM 2003, §10.2.1 (p. 285). -/
def Submodular {W : Type*} [DecidableEq W] (rho : Finset W → ℤ) : Prop :=
  rho ∅ = 0 ∧ ∀ X Y : Finset W, rho X + rho Y ≥ rho (X ∪ Y) + rho (X ∩ Y)

end DiscreteConvex.AlgorithmsC
