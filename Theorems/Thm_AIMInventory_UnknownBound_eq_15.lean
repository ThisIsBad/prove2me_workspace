import Definitions.Def_AIMInventory_UnknownBound_AIM

open MeasureTheory

namespace AIMInventory.UnknownBound

/-- Equation (15) of Appendix A applied to a round of the modified AIM run
whose projection interval contains the newsvendor comparator. -/
theorem eq_15 (P : CappedBaseStock.DemandLaw) (δ b h y₁ : ℝ) (t : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 < b) (hh : 0 < h)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (ht : 1 ≤ t)
    (hcomp : newsvendor P h b ≤ radius δ t) :
    (∫ d : CappedBaseStock.DemandPath,
        (cost P h b (modAimTarget δ b h y₁ d t) - cost P h b (newsvendor P h b))
          ∂CappedBaseStock.demandPathLaw P) ≤
      (∫ d : CappedBaseStock.DemandPath,
          (modAimTarget δ b h y₁ d t - newsvendor P h b) ^ 2
            ∂CappedBaseStock.demandPathLaw P) / (2 * stepSize b h t) -
      (∫ d : CappedBaseStock.DemandPath,
          (modAimTarget δ b h y₁ d (t + 1) - newsvendor P h b) ^ 2
            ∂CappedBaseStock.demandPathLaw P) / (2 * stepSize b h t) +
      stepSize b h t / 2 *
        (∫ d : CappedBaseStock.DemandPath,
          (signal h b (modAimTarget δ b h y₁ d t) (d (t - 1))) ^ 2
            ∂CappedBaseStock.demandPathLaw P) := by sorry

end AIMInventory.UnknownBound

