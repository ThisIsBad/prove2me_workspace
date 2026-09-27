import Mathlib
import Definitions.Def_FoundationsML_DimReduction_IsChiSquaredMGF

open MeasureTheory

namespace FoundationsML.DimReduction

/-- Lemma 15.2 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 354, PDF p. 371). Let `Q` be a random variable following a `χ²` distribution
with `k` degrees of freedom. Then, for any `0 < ε < 1/2`,
`P[(1−ε)k ≤ Q ≤ (1+ε)k] ≥ 1 − 2exp(−(ε²−ε³)k/4)`. -/
theorem chi_squared_concentration {Ω : Type*} [MeasurableSpace Ω] (Prob : Measure Ω)
    [IsProbabilityMeasure Prob] (Q : Ω → ℝ) (k : ℕ) (hQ : IsChiSquaredMGF Prob Q k)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    1 - 2 * Real.exp (-(ε ^ 2 - ε ^ 3) * k / 4) ≤
      Prob.real {ω | (1 - ε) * (k : ℝ) ≤ Q ω ∧ Q ω ≤ (1 + ε) * (k : ℝ)} := by sorry

end FoundationsML.DimReduction

