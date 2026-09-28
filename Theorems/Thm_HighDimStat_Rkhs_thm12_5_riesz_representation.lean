import Mathlib

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 12.5 (Riesz representation theorem, p. 385): every bounded linear functional `L`
on a Hilbert space `H` has a unique representer `g ∈ H` with `L(f) = ⟨f, g⟩_H` for all
`f ∈ H`. -/
theorem thm12_5_riesz_representation (L : H →ₗ[ℝ] ℝ)
    (hL : ∃ M : ℝ, ∀ f : H, |L f| ≤ M * ‖f‖) :
    ∃! g : H, ∀ f : H, L f = ⟪f, g⟫ := by sorry

end HighDimStat.Rkhs
