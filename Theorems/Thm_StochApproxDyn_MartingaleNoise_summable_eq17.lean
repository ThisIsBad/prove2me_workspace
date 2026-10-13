import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochApproxDyn.MartingaleNoise

/-- Benaïm 1999, §4.2, proof of Proposition 4.2, Eq. (17), p. 16: under the hypotheses of
Proposition 4.2, for every `T > 0`, `∑_{k ≥ 0} E(Δ(kT, T)^q) < ∞`. -/
theorem summable_eq17 {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : IsRobbinsMonro P ℱ F γ x U)
    (q : ℝ) (hq : 2 ≤ q)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n : ℕ, ∫⁻ ω, ‖U (n + 1) ω‖ₑ ^ q ∂P ≤ M)
    (hsum : Summable (fun n : ℕ => γ (n + 1) ^ (1 + q / 2))) :
    ∀ T : ℝ, 0 < T →
      ∑' k : ℕ, ∫⁻ ω, noiseDev γ (fun n => U n ω) ((k : ℝ) * T) T ^ q ∂P < ⊤ := by sorry

end StochApproxDyn.MartingaleNoise

