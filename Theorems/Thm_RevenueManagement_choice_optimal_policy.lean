import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem choice_optimal_policy {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T : ℕ) (hP : IsChoiceModel P) (hlam : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1)
    (hpos : ∀ t, 1 ≤ t → t ≤ T → 0 < lam t) (hp : ∀ j, 0 ≤ p j) :
    (∀ t x, 1 ≤ t → t ≤ T → 1 ≤ x → ∃ S, IsEfficient P p S ∧ IsChoiceOptimal lam P p T t x S ∧
      choiceValue lam P p T t x = choiceObj lam P p T t x S + choiceValue lam P p T (t + 1) x) ∧
    (∀ t x x', 1 ≤ t → t ≤ T → 1 ≤ x → x ≤ x' → ∀ S, IsEfficient P p S →
      IsChoiceOptimal lam P p T t x S → ∃ S', IsEfficient P p S' ∧
        IsChoiceOptimal lam P p T t x' S' ∧ purchaseProb P S ≤ purchaseProb P S') ∧
    (∀ t t' x, 1 ≤ t → t ≤ t' → t' ≤ T → 1 ≤ x → ∀ S, IsEfficient P p S →
      IsChoiceOptimal lam P p T t x S → ∃ S', IsEfficient P p S' ∧
        IsChoiceOptimal lam P p T t' x S' ∧ purchaseProb P S ≤ purchaseProb P S') := by sorry

end RevenueManagement
