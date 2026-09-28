import Mathlib

namespace GoldenRatioVI.Fixed

/-- The effective domain `dom g = {x | g x < +∞}` of an extended-real-valued function. -/
def effDom {E : Type*} (g : E → EReal) : Set E :=
  {x | g x ≠ ⊤}

/-- Condition (C2): `g : 𝓔 → (-∞, +∞]` is proper, convex and lower semicontinuous.
Proper: `g` never takes the value `-∞` and is finite somewhere. Convex: its epigraph
`{(x, t) | g x ≤ t}` is convex. Lower semicontinuous on all of `E`. -/
def IsProperConvexLSC {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → EReal) : Prop :=
  (∀ x, g x ≠ ⊥) ∧ (∃ x, g x ≠ ⊤) ∧
    Convex ℝ {p : E × ℝ | g p.1 ≤ (p.2 : EReal)} ∧ LowerSemicontinuous g

/-- Condition (C3): `F` is monotone on the set `D`:
`⟪F u - F v, u - v⟫ ≥ 0` for all `u, v ∈ D`. -/
def IsMonotoneOperatorOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → E) (D : Set E) : Prop :=
  ∀ u ∈ D, ∀ v ∈ D, 0 ≤ inner ℝ (F u - F v) (u - v)

/-- The solution set `S` of the variational inequality (1):
`z* ∈ dom g` with `⟪F z*, z - z*⟫ + g z - g z* ≥ 0` for every `z ∈ E`
(computed in `EReal`; since `z* ∈ dom g`, no `⊤ - ⊤` occurs for proper `g`). -/
def solutionSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : E → EReal) (F : E → E) : Set E :=
  {zs | zs ∈ effDom g ∧ ∀ z : E, (0 : EReal) ≤ ((inner ℝ (F zs) (z - zs) : ℝ) : EReal) + g z - g zs}

end GoldenRatioVI.Fixed
