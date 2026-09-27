import Mathlib
import Definitions.Def_HighDimProb_Isoperimetry_UniformProjection

open MeasureTheory

namespace HighDimProb.Isoperimetry

/-- **Lemma 5.3.2(b)** (Random projection, concentration), Vershynin, *High-Dimensional
Probability* (2018), p. 118.

Let `P` be a projection in `ℝⁿ` onto a random `m`-dimensional subspace uniformly distributed
in `G_{n,m}`. Let `z ∈ ℝⁿ` be a fixed point and `ε > 0`. Then, with probability at least
`1 − 2exp(−cε²m)`,

`(1 − ε) √(m/n) ‖z‖₂ ≤ ‖Pz‖₂ ≤ (1 + ε) √(m/n) ‖z‖₂`. -/
theorem random_projection_concentration :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (Prob : Measure Ω) [IsProbabilityMeasure Prob]
        {n : ℕ} (m : ℕ) (P : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        (hP : IsUniformProjection Prob m P) (z : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0 < ε),
        1 - 2 * Real.exp (-(c * ε ^ 2 * (m : ℝ))) ≤
          Prob.real {ω | (1 - ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖ ≤ ‖P ω z‖ ∧
            ‖P ω z‖ ≤ (1 + ε) * Real.sqrt ((m : ℝ) / (n : ℝ)) * ‖z‖} := by sorry

end HighDimProb.Isoperimetry

