import Definitions.Def_AIMInventory_UnknownBound_AIM

open MeasureTheory

namespace AIMInventory.UnknownBound

/-- Equation (10) in the proof of Theorem 7, over the rounds before the
expanding interval reaches the newsvendor quantity. -/
theorem eq_10 (P : CappedBaseStock.DemandLaw) (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 < b) (hh : 0 < h)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (hT : 1 ≤ T) :
    (∫ d : CappedBaseStock.DemandPath,
        (∑ t ∈ earlyRounds δ (newsvendor P h b) T,
          (cost P h b (modAimTarget δ b h y₁ d t) - cost P h b (newsvendor P h b)))
          ∂CappedBaseStock.demandPathLaw P) ≤
      max b h * Real.rpow (newsvendor P h b) (1 + 2 / δ) := by sorry

end AIMInventory.UnknownBound

