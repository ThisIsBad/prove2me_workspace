import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Basic

namespace CaiCandesShen.Convergence

/-- Eq. (2.14), p. 1964: for every `Y`, the minimizers over `X` of the Lagrangian
`f_τ(X) + ⟨Y, P_Ω(M - X)⟩` of problem (2.8) are exactly the minimizers of
`τ‖X‖_* + ½‖X - P_Ω Y‖_F²`. -/
theorem lagrangian_argmin_eq {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 < τ)
    (Ω : Finset (Fin n₁ × Fin n₂)) (M Y : Mat n₁ n₂) :
    {X : Mat n₁ n₂ | ∀ X' : Mat n₁ n₂,
        fτ τ X + frobInner Y (projΩ Ω (M - X)) ≤ fτ τ X' + frobInner Y (projΩ Ω (M - X'))} =
      {X : Mat n₁ n₂ | ∀ X' : Mat n₁ n₂,
        τ * nuclearNorm X + 1 / 2 * frobNorm (X - projΩ Ω Y) ^ 2 ≤
          τ * nuclearNorm X' + 1 / 2 * frobNorm (X' - projΩ Ω Y) ^ 2} := by sorry

end CaiCandesShen.Convergence
