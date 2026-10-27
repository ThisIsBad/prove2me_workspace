import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Support50.P34

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State PositiveTraceClass traceNormValue stateTraceNormTopology traceNormTopology
   operatorTrace IsPositive IsTraceClass stateEntropy relativeEntropy entropyWeight)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 11, arXiv:0904.1963v3, PDF p.38: exact weighted entropy-tail limit.
All indices are shifted together by one from the source's positive indexing. -/
theorem lemma11_weightedEntropyTail (h : ℕ → ℝ) (hmono : Monotone h)
    (hpos : ∀ j, 0 < h j) (hfinite : convergenceExponent h < ⊤) :
    Tendsto (weightedEntropyTail h) atTop (nhds (convergenceExponent h)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P34

end

