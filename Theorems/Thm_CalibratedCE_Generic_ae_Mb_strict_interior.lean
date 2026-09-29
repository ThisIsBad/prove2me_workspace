import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game

namespace CalibratedCE.Generic

theorem ae_Mb_strict_interior (m n : ℕ) :
    ∀ᵐ u₁ : Fin m → Fin n → ℝ ∂MeasureTheory.volume, ∀ a, (Mb u₁ a).Nonempty →
      ∃ p : Fin n → ℝ, (∀ b, 0 < p b) ∧ ∑ b, p b = 1 ∧
        ∀ a', a' ≠ a → ∑ b, p b * u₁ a' b < ∑ b, p b * u₁ a b := by sorry

end CalibratedCE.Generic
