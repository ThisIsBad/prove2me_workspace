import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace StochApproxDyn.SubgaussianNoise

universe u

/-- Benaïm 1999, §4.2, proof of Proposition 4.4, Eq. (18), first inequality, p. 17: there are
positive constants `C, C'` depending only on the dimension `d` and on `Γ` such that, for every
Robbins–Monro algorithm whose noise is subgaussian with constant `Γ`, and all `t ≥ 0`, `T > 0`,
`α > 0`,
`P(Δ(t, T) ≥ α) ≤ C exp(−α² / (C' ∫_t^{t+T} γ̄(s) ds))`.
`C, C'` are chosen before the probability space, the step sizes, the noise and `t, T, α`. -/
theorem deviation_tail_eq18 (d : ℕ) (Γ : ℝ) (hΓ : 0 < Γ) :
    ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧
      ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ m0) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (γ : ℕ → ℝ) (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)),
        StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U → IsSubgaussianWith P ℱ U Γ →
        ∀ t : ℝ, 0 ≤ t → ∀ T : ℝ, 0 < T → ∀ α : ℝ, 0 < α →
          P {ω | ENNReal.ofReal α ≤ StochApproxDyn.MartingaleNoise.noiseDev γ (fun n => U n ω) t T}
            ≤ ENNReal.ofReal (C * Real.exp (-α ^ 2 /
                (C' * ∫ s in t..(t + T), StochApproxDyn.MartingaleNoise.stepPath γ s))) := by sorry

end StochApproxDyn.SubgaussianNoise

