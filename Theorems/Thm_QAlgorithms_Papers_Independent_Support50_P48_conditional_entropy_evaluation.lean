import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P48

open Filter

open scoped BigOperators ENNReal NNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P30
  (PureLossBroadcastParameters thermalEntropyBits)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, entropy calculation and (12)-(13); PDF p.6, after (29).
All marginal entropies are finite for finite N. The conditional entropy is
computed from the actual TMSV output, not defined by the claimed g-difference.
The extended endpoint limit is inferred from that finite-energy difference. -/
theorem conditional_entropy_evaluation {m : ℕ} (hm : 0 < m)
    (p : PureLossBroadcastParameters m) (T : Finset (Fin m)) (hT : T.Nonempty) :
    (∀ N : ℝ≥0, IsDensity (purifiedResource p N) ∧
      (∀ S : Finset (ResourceMode m), resourceEntropyBits p N S ≠ ⊤) ∧
      reverseCutYield p N T =
        (resourceEntropyBits p N (environmentWith T)).toReal -
          (resourceEntropyBits p N (environmentWith ∅)).toReal ∧
      reverseCutYield p N T =
        thermalEntropyBits (((portWeight p none : ℝ) +
          (∑ i ∈ T, (p.transmissivity i : ℝ))) * (N : ℝ)) -
        thermalEntropyBits ((portWeight p none : ℝ) * (N : ℝ))) ∧
    Tendsto (fun N : ℝ≥0 => ENNReal.ofReal (reverseCutYield p N T))
      atTop (𝓝 (extendedCutBound p T)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P48

end

