import Mathlib

namespace TeschlQM.KatoRellich

/-- Teschl (2.66), p. 73: `R ∈ L(ℌ)` is the resolvent `R_A(z) = (A - z)⁻¹`, i.e. `A - z : 𝔇(A) → ℌ`
is a bijection and `R` is its bounded inverse: `R` maps `ℌ` into `𝔇(A)` with `(A - z) R φ = φ` for
every `φ ∈ ℌ`, and `R (A - z) ψ = ψ` for every `ψ ∈ 𝔇(A)`. -/
def IsResolventAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop :=
  (∀ φ : H, ∃ h : R φ ∈ A.domain, A ⟨R φ, h⟩ - z • R φ = φ) ∧
    ∀ ψ : A.domain, R (A ψ - z • (ψ : H)) = ψ

/-- Teschl (2.66), p. 73: the resolvent set `ρ(A) = {z ∈ ℂ | (A - z)⁻¹ ∈ L(ℌ)}`. -/
def resolventSet {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Set ℂ :=
  {z | ∃ R : H →L[ℂ] H, IsResolventAt A z R}

/-- Teschl (2.66), p. 73: the resolvent `R_A(z) = (A - z)⁻¹ ∈ L(ℌ)` for `z ∈ ρ(A)`. It is unique
when it exists (a two-sided inverse of `A - z`). Outside `ρ(A)` the value is `0`; every statement of
this mission uses `resolvent A z` only at points `z ∈ ρ(A)` (or eventually in `z`, where the book's
argument places `z` in `ρ(A)`). -/
noncomputable def resolvent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) (z : ℂ) : H →L[ℂ] H :=
  open Classical in
  if h : ∃ R : H →L[ℂ] H, IsResolventAt A z R then h.choose else 0

end TeschlQM.KatoRellich
