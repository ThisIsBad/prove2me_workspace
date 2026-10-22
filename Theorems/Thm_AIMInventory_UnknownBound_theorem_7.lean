import Definitions.Def_AIMInventory_UnknownBound_AIM

open MeasureTheory

namespace AIMInventory.UnknownBound

/-- Theorem 7: average expected newsvendor regret of expanding-projection
AIM in the perishable inventory case, without a known upper bound. -/
theorem theorem_7 (P : CappedBaseStock.DemandLaw) (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 < b) (hh : 0 < h)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (hT : 1 ≤ T) :
    (∫ d : CappedBaseStock.DemandPath,
        ((∑ t ∈ Finset.Icc 1 T, cost P h b (modAimTarget δ b h y₁ d t)) / (T : ℝ))
          ∂CappedBaseStock.demandPathLaw P) - cost P h b (newsvendor P h b) ≤
      max b h *
        (1 / Real.rpow (T : ℝ) ((1 / 2 : ℝ) - δ) +
         1 / Real.rpow (T : ℝ) (1 / 2 : ℝ) +
         Real.rpow (newsvendor P h b) (1 + 2 / δ) / (T : ℝ)) := by sorry

end AIMInventory.UnknownBound

