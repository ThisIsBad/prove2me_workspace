import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem units_in_resupply_poisson_finite_time {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (x : ℕ) :
    (P {ω | S.unitsInResupply t ω = x}).toReal =
      Real.exp (-(S.rate * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u))) *
        (S.rate * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x / (Nat.factorial x : ℝ) := by sorry

end ServiceParts.Palm

