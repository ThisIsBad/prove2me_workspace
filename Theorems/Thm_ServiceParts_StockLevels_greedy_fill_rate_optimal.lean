import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems

namespace ServiceParts.StockLevels

theorem greedy_fill_rate_optimal {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (lam tbar c : ι → ℝ) (hlam : ∀ i, 0 < lam i) (htbar : ∀ i, 0 < tbar i)
    (hc : ∀ i, 0 < c i) (seq : ℕ → ι → ℕ) (hseq : IsGreedySeq lam tbar c seq) (k : ℕ) :
    (∀ i, ⌊lam i * tbar i⌋₊ ≤ seq k i) ∧
    ∀ s : ι → ℕ, (∀ i, ⌊lam i * tbar i⌋₊ ≤ s i) →
      ∑ i, c i * (s i : ℝ) ≤ ∑ i, c i * (seq k i : ℝ) →
      avgFillRate lam tbar s ≤ avgFillRate lam tbar (seq k) := by sorry

end ServiceParts.StockLevels

