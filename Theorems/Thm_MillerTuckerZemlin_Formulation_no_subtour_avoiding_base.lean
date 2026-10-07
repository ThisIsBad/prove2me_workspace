import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem no_subtour_avoiding_base (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ)
    (u : Fin (n + 1) → ℝ) (hx : Feasible n p x u) (k : ℕ) (r : Fin (k + 1) → Fin (n + 1))
    (hr : ∀ i, r i ≠ 0) : ¬ ∀ i : Fin (k + 1), x (r i) (r (i + 1)) = 1 := by sorry

end MillerTuckerZemlin.Formulation

