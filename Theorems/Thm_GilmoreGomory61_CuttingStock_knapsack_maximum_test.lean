import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Knapsack

namespace GilmoreGomory61.CuttingStock

/-- A maximum pattern tests the compatibility of (6) and (7), pp. 852–853. -/
theorem knapsack_maximum_test {m k : ℕ} (I : Instance m k)
    (hℓ : ∀ i, 0 < I.ℓ i) (b : Fin m → ℝ) (L c : ℝ) (hL : 0 ≤ L) :
    ∃ aStar : Fin m → ℕ,
      patLen I aStar ≤ L ∧
      (∀ a : Fin m → ℕ, patLen I a ≤ L →
        (∑ i, b i * (a i : ℝ)) ≤ ∑ i, b i * (aStar i : ℝ)) ∧
      knapF I b m L = ((∑ i, b i * (aStar i : ℝ) : ℝ) : EReal) ∧
      ((∃ a : Fin m → ℕ, patLen I a ≤ L ∧
        c < ∑ i, b i * (a i : ℝ)) ↔ c < ∑ i, b i * (aStar i : ℝ)) := by sorry

end GilmoreGomory61.CuttingStock

