import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §8.1, p. 232: a trapping region for the flow is an open connected set `E` whose
closure is compact (and contained in the phase space `M`, where the flow lives) with
`Φ_t(Ē) ⊂ E` for all `t > 0`: every `x ∈ Ē` has `t ∈ I x` and `Φ t x ∈ E` for all `t > 0`.
`IsConnected` includes nonemptiness. -/
def IsTrappingRegion {X : Type*} [NormedAddCommGroup X] (M : Set X) (I : X → Set ℝ)
    (Φ : ℝ → X → X) (E : Set X) : Prop :=
  IsOpen E ∧ IsConnected E ∧ IsCompact (closure E) ∧ closure E ⊆ M ∧
    ∀ x ∈ closure E, ∀ t : ℝ, 0 < t → t ∈ I x ∧ Φ t x ∈ E

end TeschlODE.HigherDim
