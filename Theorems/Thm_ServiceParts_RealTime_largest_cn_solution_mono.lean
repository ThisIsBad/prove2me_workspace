import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory

namespace ServiceParts.RealTime

/-- Eq. (10.20), p. 237: for `t ∈ [T^r_{ij}, …, T^r_{ij} + T_{i0}]`, the largest optimal
solutions of the constrained newsvendor problems satisfy `Ŝ_{ij(t-1)} ≤ Ŝ_{ijt}`. -/
theorem largest_cn_solution_mono {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ)
    (ht₁ : M.Tr j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) (s s' : ℤ)
    (hs : M.IsLargestCNSolution j (t - 1) s) (hs' : M.IsLargestCNSolution j t s') :
    s ≤ s' := by sorry

end ServiceParts.RealTime

