import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model
import Definitions.Def_ServiceParts_RealTime_SAM

open MeasureTheory

namespace ServiceParts.RealTime

/-- Theorem 15, p. 237: let `Ŝ_{ijt}` be the largest optimal solution of `CN_{ijt}` for
`t ∈ [T^r_{ij}, …, T^r_{ij} + T_{i0}]`. In every optimal solution of `SAM_i`, the cumulative
supply satisfies `S̃_{ij(T^r_{ij}-1)} ≤ S*_{ijt} ≤ Ŝ_{ijt}` (10.21) for all bases `j` and all
`t ∈ [T^r_{ij}, …, T^r_{ij} + T_{i0}]`. -/
theorem theorem15 {J : Type*} [Fintype J] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Tr j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (y : J → ℕ → ℕ) (hy : IsSAMOptimal M y) (j : J) (t : ℕ)
    (ht₁ : M.Tr j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) :
    M.baseSupply j (M.Tr j - 1) ≤ samStock M y j t ∧ samStock M y j t ≤ Shat j t := by sorry

end ServiceParts.RealTime

