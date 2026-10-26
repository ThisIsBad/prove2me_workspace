import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_NearestNeighbor_Weights

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem proposition_12 {d : ℕ} (s : ScaleSeq d) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hs0 : ∀ n x xs j, 0 ≤ s n x xs j) (h7 : Cond7 s a b)
    (c : ℕ → ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) (hc : IsCoeffRow c n)
    (x : EuclideanSpace ℝ (Fin d)) (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    (∑ i, swapW (nnWeights c s) n x xs i) ≤ (beta d (a / b) : ℝ) := by sorry

end StoneRegression.NearestNeighbor

