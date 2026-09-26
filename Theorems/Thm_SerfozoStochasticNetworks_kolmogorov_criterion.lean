import Mathlib
import Definitions.Def_SerfozoStochasticNetworks_Reversible

namespace SerfozoStochasticNetworks

theorem kolmogorov_criterion {E : Type*} (q : E → E → ℝ)
    (hq : ∀ x y, 0 ≤ q x y) (htw : TwoWay q) (hirr : IsIrreducible q) :
    (IsReversible q ↔ KolmogorovCriterion q) ∧ (IsReversible q ↔ RatioInvariance q) ∧
    (IsReversible q → ∀ x₀ : E, ∃ π : E → ℝ, (∀ x, 0 < π x) ∧ π x₀ = 1 ∧ DetailedBalance q π ∧
      ∀ (n : ℕ) (p : Fin (n + 1) → E), IsPath q p → p 0 = x₀ →
        π (p (Fin.last n)) = pathRatio q p) := by sorry

end SerfozoStochasticNetworks
