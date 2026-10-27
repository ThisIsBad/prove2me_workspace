import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_VectorOptimization
import Definitions.Def_NashVecOpt_SharedConstraint_Game

namespace NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Objective (5), p. 6: retain strategies as well as every player's cost. -/
def obj (f : ι → (∀ j, E j) → ℝ) (x : ∀ j, E j) :
    (∀ j, E j) × (ι → ℝ) := (x, fun i => f i x)

/-- Ordering cone (6), p. 6: some player's cost coordinate is nonnegative and all other
strategy coordinates vanish. -/
def orderCone : Set ((∀ j, E j) × (ι → ℝ)) :=
  {z | ∃ i, (∀ j, j ≠ i → z.1 j = 0) ∧ 0 ≤ z.2 i}

/-- The player-indexed product cone (7), p. 6. -/
def coneI (i : ι) : Set ((∀ j, E j) × (ι → ℝ)) :=
  (Set.univ.pi fun j => if j = i then (Set.univ : Set (E j)) else {0}) ×ˢ
  (Set.univ.pi fun j => if j = i then Set.Ici (0 : ℝ) else Set.univ)

end NashVecOpt.SharedConstraint
