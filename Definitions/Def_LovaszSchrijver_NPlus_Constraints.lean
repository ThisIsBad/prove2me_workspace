import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_StableSet

namespace LovaszSchrijver.NPlus

/-- `C` induces a chordless odd cycle (an odd hole, triangles included) in `G`: for some odd
`m ≥ 3` the nodes of `C` can be numbered `0, …, m-1` so that two of them are adjacent in `G`
exactly when their numbers are consecutive modulo `m` (pp. 175–176). -/
def IsOddHole {V : Type} (G : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ ∃ f : Fin m ≃ C, ∀ s t : Fin m,
    G.Adj (f s : V) (f t : V) ↔ (t.val = (s.val + 1) % m ∨ s.val = (t.val + 1) % m)

/-- `D` induces a chordless odd cycle in the complement of `G` with at least `5` nodes
(an odd antihole, p. 176). -/
def IsOddAntihole {V : Type} (G : SimpleGraph V) (D : Finset V) : Prop :=
  5 ≤ D.card ∧ IsOddHole Gᶜ D

/-- `U` induces an odd wheel in `G` with center `u₀ ∈ U` (p. 176): `U \ {u₀}` is an odd hole
and `u₀` is adjacent to every node of it. -/
def IsOddWheel {V : Type} [DecidableEq V] (G : SimpleGraph V) (U : Finset V) (u₀ : V) : Prop :=
  u₀ ∈ U ∧ IsOddHole G (U.erase u₀) ∧ ∀ w ∈ U.erase u₀, G.Adj u₀ w

/-- Coefficient vector of the wheel constraint (p. 176):
`Σ_{i ∈ U \ {u₀}} xᵢ + ((|U| - 2)/2) x_{u₀} ≤ (|U| - 2)/2`. -/
noncomputable def wheelCoeff {V : Type} [DecidableEq V] (U : Finset V) (u₀ : V) : V → ℝ :=
  fun i => if i = u₀ then ((U.card : ℝ) - 2) / 2 else if i ∈ U then 1 else 0

end LovaszSchrijver.NPlus
