import Mathlib

namespace TeschlQM.KatoRellich

open scoped ENNReal

/-- Teschl (6.1), p. 133: `B` is `A` bounded *with constants* `a, b`: `𝔇(A) ⊆ 𝔇(B)`, `a, b ≥ 0`, and
`‖Bψ‖ ≤ a‖Aψ‖ + b‖ψ‖` for all `ψ ∈ 𝔇(A)`. The domain inclusion is part of the definition, as in the
book. -/
def IsRelativelyBoundedWith {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ.[ℂ] H) (a b : ℝ) : Prop :=
  A.domain ≤ B.domain ∧ 0 ≤ a ∧ 0 ≤ b ∧
    ∀ (ψ : H) (hA : ψ ∈ A.domain) (hB : ψ ∈ B.domain),
      ‖B ⟨ψ, hB⟩‖ ≤ a * ‖A ⟨ψ, hA⟩‖ + b * ‖ψ‖

/-- Teschl, p. 133: `B` is *`A` bounded* (relatively bounded with respect to `A`) if `𝔇(A) ⊆ 𝔇(B)`
and there are constants `a, b ≥ 0` such that (6.1) holds. -/
def IsRelativelyBounded {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ.[ℂ] H) : Prop :=
  ∃ a b : ℝ, IsRelativelyBoundedWith A B a b

/-- Teschl, p. 133: the *`A`-bound* of `B`, the infimum of all constants `a` for which a
corresponding `b` exists such that (6.1) holds. It takes values in `[0, ∞]`; it is `∞` exactly when
`B` is not `A` bounded (the infimum over the empty set), so it is never a junk `0`. -/
noncomputable def relativeBound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : H →ₗ.[ℂ] H) : ℝ≥0∞ :=
  ⨅ (a : ℝ) (_ : ∃ b : ℝ, IsRelativelyBoundedWith A B a b), ENNReal.ofReal a

end TeschlQM.KatoRellich
