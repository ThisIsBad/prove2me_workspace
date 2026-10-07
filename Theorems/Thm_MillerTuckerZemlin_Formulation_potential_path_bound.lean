import Mathlib
import Definitions.Def_MillerTuckerZemlin_Formulation_Model

namespace MillerTuckerZemlin.Formulation

theorem potential_path_bound (n p : ℕ) (x : Fin (n + 1) → Fin (n + 1) → ℕ) (u : Fin (n + 1) → ℝ)
    (hx : Feasible n p x u) (m : ℕ) (r : Fin (m + 1) → Fin (n + 1))
    (hr : ∀ k, r k ≠ 0) (hpath : ∀ k : Fin m, x (r k.castSucc) (r k.succ) = 1) :
    u (r 0) - u (r (Fin.last m)) ≤ -(m : ℝ) := by sorry

end MillerTuckerZemlin.Formulation

