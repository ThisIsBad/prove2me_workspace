import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Knapsack

namespace GilmoreGomory61.CuttingStock

/-- The Fₛ recursion and its finite range from p. 853. Earlier lengths must be positive too. -/
theorem knapsack_dp_recursion {m k : ℕ} (I : Instance m k)
    (b : Fin m → ℝ) (s : ℕ) (hs : s < m)
    (hℓ : ∀ i : Fin m, i.val ≤ s → 0 < I.ℓ i) (x : ℝ) :
    knapF I b (s + 1) x =
      ⨆ r ∈ Finset.range (⌊x / I.ℓ ⟨s, hs⟩⌋₊ + 1),
        (((r : ℝ) * b ⟨s, hs⟩ : ℝ) : EReal) +
          knapF I b s (x - r * I.ℓ ⟨s, hs⟩) := by sorry

end GilmoreGomory61.CuttingStock

