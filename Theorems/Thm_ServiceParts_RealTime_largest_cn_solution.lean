import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model

open MeasureTheory

namespace ServiceParts.RealTime

/-- Eq. (10.19), p. 237: the constrained newsvendor problem `CN_{ijt}` has a largest optimal
solution, namely `Ŝ_{ijt} = max(S̃_{ijt}, s⁰)`, where `s⁰` is the least integer `s` with
`F_{X_{ijt}}(s) > b_{ij}/(b_{ij} + h_{ij})` (the integer critical fractile of the demand). -/
theorem largest_cn_solution {J : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (j : J) (t : ℕ) :
    (∃ s0 : ℤ, IsLeast {s : ℤ | M.b j / (M.b j + M.h j) < M.demandCDF j t s} s0) ∧
      ∀ s0 : ℤ, IsLeast {s : ℤ | M.b j / (M.b j + M.h j) < M.demandCDF j t s} s0 →
        M.IsLargestCNSolution j t (max (M.baseSupply j t) s0) := by sorry

end ServiceParts.RealTime

