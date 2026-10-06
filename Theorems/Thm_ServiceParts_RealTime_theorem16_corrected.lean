import Mathlib
import Definitions.Def_ServiceParts_RealTime_Model
import Definitions.Def_ServiceParts_RealTime_ESAM

open MeasureTheory

namespace ServiceParts.RealTime

/-- Theorem 16, p. 244, corrected. Let `Ŝ_{ijk}` be the largest optimal solution of
`CN_{ijk}` for `k ∈ [T^e_{ij}, …, T^r_{ij} + T_{i0}]` and
`M_{jt} = max_{k∈[T^e_{ij},…,t]} {Ŝ_{ijk} - S̃_{ijk}}` (10.43). In every optimal solution of
`ESAM_i`, for every base `j` and `t ∈ [T^e_{ij}, …, T^r_{ij} + T_{i0}]`,
`S̃_{ijt} ≤ S*_{ijt}`, and `S*_{ijt} ≤ S̃_{ijt} + M_{jt}` (10.44) provided
`T^r_{ij} = T^e_{ij} + 1` or `t < T^e_{ij} + T_{i0}`. (The upper bound as printed, without
this proviso, is false: see `theorem16_counterexample`.) -/
theorem theorem16_corrected {J : Type*} [Fintype J] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (M : ItemModel J Ω P) (Shat : J → ℕ → ℤ)
    (hShat : ∀ j k, M.Te j ≤ k → k ≤ M.Tr j + M.T0 → M.IsLargestCNSolution j k (Shat j k))
    (yr ye : J → ℕ → ℕ) (hy : IsESAMOptimal M yr ye) (j : J) (t : ℕ)
    (ht₁ : M.Te j ≤ t) (ht₂ : t ≤ M.Tr j + M.T0) :
    M.baseSupply j t ≤ esamStock M yr ye j t ∧
      (M.Tr j = M.Te j + 1 ∨ t < M.Te j + M.T0 →
        esamStock M yr ye j t ≤ M.baseSupply j t +
          (Finset.Icc (M.Te j) t).sup' ⟨M.Te j, Finset.left_mem_Icc.mpr ht₁⟩
            (fun k => Shat j k - M.baseSupply j k)) := by sorry

end ServiceParts.RealTime

