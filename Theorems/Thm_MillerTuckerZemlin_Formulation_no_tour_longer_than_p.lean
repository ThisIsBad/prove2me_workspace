import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem no_tour_longer_than_p (n p : ℕ) (hp : 1 ≤ p) (x : Fin (n + 1) → Fin (n + 1) → ℕ)
    (u : Fin (n + 1) → ℝ) (hx : Feasible n p x u) (r : Fin (p + 1) → Fin (n + 1))
    (hr : ∀ k, r k ≠ 0) (h0 : x 0 (r 0) = 1) :
    ¬ ∀ k : Fin p, x (r k.castSucc) (r k.succ) = 1 := by sorry

end MillerTuckerZemlin.Formulation

