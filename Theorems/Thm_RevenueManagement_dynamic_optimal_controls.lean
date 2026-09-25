import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem dynamic_optimal_controls (lam : ℕ → ℕ → ℝ) (p : ℕ → ℝ) (n T C : ℕ)
    (hlam : IsArrivalModel lam n) (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) (t : ℕ) (ht : 1 ≤ t)
    (htT : t ≤ T) :
    (∀ j, dynProtLevel lam p n T C t j ≤ dynProtLevel lam p n T C t (j + 1)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if dynProtLevel lam p n T C t (j - 1) < x then 1 else 0)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if C - x < dynBookLimit lam p n T C t j then 1 else 0)) ∧
    (∀ j x, 1 ≤ j → j ≤ n → 1 ≤ x → x ≤ C →
      IsDynOptimal lam p n T t x j (if dynBidPrice lam p n T (t + 1) x ≤ p j then 1 else 0)) := by sorry

end RevenueManagement
