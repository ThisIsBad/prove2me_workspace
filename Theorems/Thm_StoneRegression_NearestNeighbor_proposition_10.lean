import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_NearestNeighbor_Weights

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem proposition_10 {d : ℕ} (a b : ℝ) (bv : Fin d → ℝ) (ha : 0 < a) (hbv : ∀ j, a ≤ bv j ∧ bv j ≤ b)
    (V : Set (EuclideanSpace ℝ (Fin d))) (hV : V ∈ ConeFamily d (a / b))
    (u v : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V) (hv : v ∈ V) (hu0 : 0 < ‖u‖) (huv : ‖u‖ ≤ ‖v‖) :
    ‖coordScale bv v - coordScale bv u‖ < ‖coordScale bv v‖ := by sorry

end StoneRegression.NearestNeighbor

