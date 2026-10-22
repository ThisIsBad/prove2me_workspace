import Definitions.Def_AIMInventory_UnknownBound_AIM

open MeasureTheory

namespace AIMInventory.UnknownBound

/-- Equation (11) in the proof of Theorem 7, over the rounds whose
projection interval contains the newsvendor quantity. -/
theorem eq_11 (P : CappedBaseStock.DemandLaw) (δ b h y₁ : ℝ) (T : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 < b) (hh : 0 < h)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (hT : 1 ≤ T) :
    (∫ d : CappedBaseStock.DemandPath,
        (∑ t ∈ lateRounds δ (newsvendor P h b) T,
          (cost P h b (modAimTarget δ b h y₁ d t) - cost P h b (newsvendor P h b)))
          ∂CappedBaseStock.demandPathLaw P) ≤
      max b h * Real.rpow (T : ℝ) ((1 / 2 : ℝ) + δ) +
        max b h * Real.rpow (T : ℝ) (1 / 2 : ℝ) := by sorry

end AIMInventory.UnknownBound

