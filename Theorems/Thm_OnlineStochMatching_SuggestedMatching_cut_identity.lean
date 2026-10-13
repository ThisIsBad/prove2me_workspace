import Definitions.Def_OnlineStochMatching_SuggestedMatching_Cut
import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm

namespace OnlineStochMatching.SuggestedMatching

/-- Section 4.1's canonical cut has no advertiser-to-type crossing edge,
and its capacity equals the maximum integral flow. -/
theorem cut_identity (A I : Type) [Fintype A] [Fintype I]
    (inst : Instance A I) (M : Finset (A × I)) (hM : IsMaxBMatching inst M) :
    (∀ a i, (a, i) ∈ inst.E → adInSourceSide inst M a → typeInSourceSide inst M i) ∧
      (coveredAds M).card =
        (adsInSinkSide inst M).card +
          ∑ i ∈ typesInSourceSide inst M, inst.e i := by sorry

end OnlineStochMatching.SuggestedMatching

