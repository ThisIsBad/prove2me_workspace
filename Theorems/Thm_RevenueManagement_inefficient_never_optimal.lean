import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem inefficient_never_optimal {n : ℕ} (lam : ℕ → ℝ) (P : Finset (Fin n) → Fin n → ℝ)
    (p : Fin n → ℝ) (T : ℕ) (hP : IsChoiceModel P) (hlam : ∀ t, 0 ≤ lam t ∧ lam t ≤ 1)
    (hp : ∀ j, 0 ≤ p j) (t x : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hx : 1 ≤ x) (hpos : 0 < lam t)
    (S : Finset (Fin n)) (hS : IsInefficient P p S) :
    ¬ IsChoiceOptimal lam P p T t x S := by sorry

end RevenueManagement
