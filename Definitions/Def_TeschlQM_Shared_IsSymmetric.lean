import Mathlib

namespace TeschlQM.Shared

open scoped InnerProductSpace

/-- Teschl (2.17), p. 58: a linear operator `A : 𝔇(A) → ℌ` (a `LinearPMap`) is *symmetric* if it is
densely defined and `⟨φ, Aψ⟩ = ⟨Aφ, ψ⟩` for all `ψ, φ ∈ 𝔇(A)`. Density is part of the book's
definition. -/
def IsSymmetric {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Prop :=
  Dense (A.domain : Set H) ∧ ∀ φ ψ : A.domain, ⟪(φ : H), A ψ⟫_ℂ = ⟪A φ, (ψ : H)⟫_ℂ

end TeschlQM.Shared
