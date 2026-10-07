import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting

namespace ChenStein.OneVar

open scoped NNReal

/-- Arratia--Goldstein--Gordon (1989), §4, p. 20: S is inverse to T. -/
theorem T_comp_S (lam : ℝ≥0) (hlam : 0 < lam) (h : ℕ → ℝ) :
    ∀ w : ℕ, T lam (S lam h) w = h w := by sorry

end ChenStein.OneVar

