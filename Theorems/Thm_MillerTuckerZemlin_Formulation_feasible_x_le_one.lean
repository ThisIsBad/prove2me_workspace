import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem feasible_x_le_one (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) : ∀ i j : Fin (n + 1), x i j ≤ 1 := by sorry

end MillerTuckerZemlin.Formulation

