import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope

namespace ChvatalPolytopes.Neighbors

/-- The value `cx = Σ (c_u x_u : u ∈ V)` of an integer-valued vector `c` at a real vector `x`. -/
def intDot {V : Type*} [Fintype V] (c : V → ℤ) (x : V → ℝ) : ℝ :=
  ∑ u, (c u : ℝ) * x u

/-- **Neighbours in `P(G)`** (Chvátal 1975, p. 149, first sentence of the proof of Theorem 6.2):
`y` and `z` are neighbours in `P(G)` if and only if there is an integer-valued vector
`c = (c_u : u ∈ V)` such that `y` and `z` are the only two vectors which maximize `cx` over `S(G)`.

"The only two" is spelled out as: `y ≠ z`, and for some `c : V → ℤ` the set of maximizers of
`cx` over `S(G)` is exactly `{y, z}`. -/
def AreNeighbors {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (y z : V → ℝ) : Prop :=
  y ≠ z ∧ ∃ c : V → ℤ,
    {x | x ∈ stableVectors G ∧ ∀ x' ∈ stableVectors G, intDot c x' ≤ intDot c x} = {y, z}

end ChvatalPolytopes.Neighbors
