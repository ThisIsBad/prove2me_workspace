import Mathlib
import Definitions.Def_FoundationsML_DimReduction_IsIIDStandardGaussianMatrix
import Definitions.Def_FoundationsML_DimReduction_SqNorm

open MeasureTheory

namespace FoundationsML.DimReduction

/-- Lemma 15.3 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 355, PDF p. 372). Let `x ∈ ℝ^N`, define `k < N` and assume that entries in
`A ∈ ℝ^{k×N}` are sampled independently from the standard normal distribution `N(0,1)`. Then,
for any `0 < ε < 1/2`,
`P[(1−ε)‖x‖² ≤ ‖(1/√k)Ax‖² ≤ (1+ε)‖x‖²] ≥ 1 − 2exp(−(ε²−ε³)k/4)`. -/
theorem gaussian_projection_distortion {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    [IsProbabilityMeasure Prob] {N k : ℕ} (hk : k < N)
    (A : Ω → Matrix (Fin k) (Fin N) ℝ) (hA : IsIIDStandardGaussianMatrix Prob A)
    (x : Fin N → ℝ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    1 - 2 * Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) ≤
      Prob.real {ω | (1 - ε) * SqNorm x ≤
          SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) ∧
        SqNorm (fun j => (1 / Real.sqrt k) * (A ω).mulVec x j) ≤ (1 + ε) * SqNorm x} := by sorry

end FoundationsML.DimReduction

