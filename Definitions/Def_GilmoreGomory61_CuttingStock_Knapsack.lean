import Mathlib
import Definitions.Def_GilmoreGomory61_CuttingStock_Model

namespace GilmoreGomory61.CuttingStock

/-- The extended-real knapsack value Fₛ(x), p. 853. It is bottom if no pattern fits. -/
noncomputable def knapF {m k : ℕ} (I : Instance m k) (b : Fin m → ℝ)
    (s : ℕ) (x : ℝ) : EReal :=
  ⨆ (a : Fin m → ℕ) (_ : (∀ i : Fin m, s ≤ i.val → a i = 0) ∧ patLen I a ≤ x),
    ((∑ i, b i * (a i : ℝ) : ℝ) : EReal)

end GilmoreGomory61.CuttingStock
