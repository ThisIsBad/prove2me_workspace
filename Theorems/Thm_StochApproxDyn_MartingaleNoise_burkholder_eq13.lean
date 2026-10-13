import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StochApproxDyn.MartingaleNoise

universe u

/-- Benaïm 1999, §4.2, proof of Proposition 4.2, Eq. (13), p. 15: the instance of Burkholder's
inequality used in the proof. For `q ≥ 2` there is a constant `C_q > 0` (depending only on `q`
and the dimension `d`) such that for every Robbins–Monro algorithm, every `n` and every `T > 0`,
`E sup_{n<k≤m(τ_n+T)} ‖∑_{i=n}^{k-1} γ_{i+1}U_{i+1}‖^q ≤ C_q E[(∑_{i=n}^{m(τ_n+T)-1} γ_{i+1}² ‖U_{i+1}‖²)^{q/2}]`. -/
theorem burkholder_eq13 (d : ℕ) (q : ℝ) (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type u} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℕ m0) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
        (γ : ℕ → ℝ) (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)),
        IsRobbinsMonro P ℱ F γ x U →
        ∀ (n : ℕ) (T : ℝ), 0 < T →
          ∫⁻ ω, (Finset.Ioc n (stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T))).sup
              (fun k => ‖∑ i ∈ Finset.Ico n k, γ (i + 1) • U (i + 1) ω‖ₑ ^ q) ∂P
            ≤ ENNReal.ofReal C *
              ∫⁻ ω, (∑ i ∈ Finset.Ico n (stepIndex γ (StochApproxDyn.Interpolation.tau γ n + T)),
                  ENNReal.ofReal (γ (i + 1) ^ 2) * ‖U (i + 1) ω‖ₑ ^ (2 : ℝ)) ^ (q / 2) ∂P := by sorry

end StochApproxDyn.MartingaleNoise

