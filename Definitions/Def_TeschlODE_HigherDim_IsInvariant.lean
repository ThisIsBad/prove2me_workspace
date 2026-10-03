import Mathlib

namespace TeschlODE.HigherDim

/-- Teschl, §6.3, p. 193: a set `Λ ⊆ M` is invariant if it contains the orbit
`γ(x) = Φ(I_x, x)` of each of its points: `Φ t x ∈ Λ` for every `x ∈ Λ` and `t ∈ I x`. -/
def IsInvariant {E : Type*} (M : Set E) (I : E → Set ℝ) (Φ : ℝ → E → E) (Λ : Set E) :
    Prop :=
  Λ ⊆ M ∧ ∀ x ∈ Λ, ∀ t ∈ I x, Φ t x ∈ Λ

end TeschlODE.HigherDim
