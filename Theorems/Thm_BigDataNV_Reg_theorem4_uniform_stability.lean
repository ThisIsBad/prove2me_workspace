import Mathlib
import Definitions.Def_BigDataNV_Reg_Setting

namespace BigDataNV.Reg

/-- Theorem 4, p. 30: (NV-reg) is uniformly stable with respect to the newsvendor cost, with
stability parameter `(b ∨ h)² X²_max / (2 n λ)`, in the form used by Theorem 5 (p. 31): the
comparison solution minimizes the leave-one-out objective with weight `1/n`. -/
theorem theorem4_uniform_stability {p n : ℕ} (b h lam Xmax : ℝ)
    (hb : 0 < b) (hh : 0 < h) (hlam : 0 < lam) (hX : 0 ≤ Xmax)
    (S : Fin n → EuclideanSpace ℝ (Fin p) × ℝ) (hS : ∀ j, ‖(S j).1‖ ^ 2 ≤ Xmax ^ 2)
    (i : Fin n) (q q' : EuclideanSpace ℝ (Fin p))
    (hq : IsNVRegSolution b h lam S q) (hq' : IsNVRegLooSolution b h lam S i q') :
    ∀ x : EuclideanSpace ℝ (Fin p), ‖x‖ ^ 2 ≤ Xmax ^ 2 → ∀ d : ℝ,
      |nvCost b h (inner ℝ q x) d - nvCost b h (inner ℝ q' x) d| ≤
        (max b h) ^ 2 * Xmax ^ 2 / (2 * (n : ℝ) * lam) := by sorry

end BigDataNV.Reg

