import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem choice_marginal_values {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T : ℕ) (hP : IsChoiceModel P) (hlam : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1)
    (hp : ∀ j, 0 ≤ p j) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x) :
    choiceDelta lam P p T t (x + 1) ≤ choiceDelta lam P p T t x ∧
      choiceDelta lam P p T (t + 1) x ≤ choiceDelta lam P p T t x := by sorry

end RevenueManagement
