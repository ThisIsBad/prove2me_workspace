import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochApproxDyn.MartingaleNoise

/-- Benaïm 1999, §4.2, proof of Proposition 4.2, Eq. (16), p. 15: for a Robbins–Monro algorithm
with `q ≥ 2` and `sup_n E‖U_{n+1}‖^q < ∞`, for every `T > 0` there is `C(q, T) > 0` (independent
of `t`) with `E(Δ(t, T)^q) ≤ C(q, T) ∫_t^{t+T} γ̄(s)^{q/2} ds` for all `t ≥ 0`. -/
theorem moment_bound_eq16 {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : IsRobbinsMonro P ℱ F γ x U)
    (q : ℝ) (hq : 2 ≤ q)
    (hmom : ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n : ℕ, ∫⁻ ω, ‖U (n + 1) ω‖ₑ ^ q ∂P ≤ M) :
    ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, noiseDev γ (fun n => U n ω) t T ^ q ∂P ≤
        ENNReal.ofReal C * ∫⁻ s in Set.Icc t (t + T), ENNReal.ofReal (stepPath γ s ^ (q / 2)) := by sorry

end StochApproxDyn.MartingaleNoise

