import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

theorem reversible_canonical_form {E : Type*} (q : E → E → ℝ) (π : E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (hπ : ∀ x, 0 < π x) :
    DetailedBalance q π ↔ ∃ γ : E → E → ℝ, (∀ x y, 0 ≤ γ x y) ∧ (∀ x y, γ x y = γ y x) ∧
      ∀ x y, q x y = γ x y / π x := by sorry

end SerfozoStochasticNetworks
