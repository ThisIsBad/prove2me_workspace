import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace RevenueManagement

theorem static_optimal_controls (p : ℕ → ℝ) (f : ℕ → ℕ → ℝ) (hf : ∀ j, IsPmf (f j))
    (hp : ∀ j, 0 ≤ p j) (hanti : Antitone p) (C : ℕ) :
    (∀ j, protLevel p f C j ≤ protLevel p f C (j + 1)) ∧
    (∀ j x d, x ≤ C → IsStageOptimal p f j x d (min (x - protLevel p f C j) d)) ∧
    (∀ j x d, x ≤ C → IsStageOptimal p f j x d (min (bookLimit p f C (j + 1) - (C - x)) d)) ∧
    (∀ j x d, x ≤ C → IsStageOptimal p f j x d (bidControl p f j x d)) := by sorry

end RevenueManagement
