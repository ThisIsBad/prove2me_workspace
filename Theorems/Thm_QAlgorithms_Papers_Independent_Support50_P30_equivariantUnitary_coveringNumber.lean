import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF p.15, Theorem 5: exponent 2*Te_(n+1), internal centers in the full
commuting family, and spectral norm. PRINTED: the radius has no stated domain.
CHANGED: require 0 < epsilon <= 1, retaining the formula and family.
WHY: the invoked small-radius unitary-cover estimate applies in this regime;
for epsilon > 6 the printed bound is below one for a nonempty family.
The fixed cutoff 1 is a conservative small-radius choice, not a maximal domain. -/
theorem equivariantUnitary_coveringNumber (n : ℕ) (epsilon : ℝ≥0)
    (hpos : 0 < epsilon) (hsmall : epsilon ≤ 1) :
    (Metric.coveringNumber epsilon (unitaryFamily n) : ℝ≥0∞) ≤
      ENNReal.ofReal ((6 / (epsilon : ℝ)) ^ (2 * (n + 3).choose 3)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end

