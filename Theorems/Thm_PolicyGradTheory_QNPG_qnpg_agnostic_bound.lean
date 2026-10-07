import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting

namespace PolicyGradTheory.QNPG

open FoundationsML.ReinforcementLearning MeasureTheory

/-- Theorem 6.1, p. 29: agnostic Q-NPG for a log-linear policy class. -/
theorem qnpg_agnostic_bound {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Nonempty A] (d : ℕ)
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : PolicyGradTheory.ProjGA.IsFiniteMDP P r γ)
    (ρ : S → ℝ) (hρ : PolicyGradTheory.ProjGA.IsDist ρ)
    (ν : S × A → ℝ) (hν : PolicyGradTheory.ProjGA.IsDist ν)
    (πstar : S → A → ℝ) (hπstar : IsPolicy πstar)
    (φ : S → A → EuclideanSpace ℝ (Fin d))
    (B : ℝ) (hB : 0 < B) (hφ : ∀ s a, ‖φ s a‖ ≤ B)
    (W : ℝ) (hW : 0 < W)
    (κ : ℝ) (hκnonneg : 0 ≤ κ)
    (hκ : ∀ v, quadForm φ (dstar P γ ρ πstar) v ≤ κ * quadForm φ ν v)
    (T : ℕ) (hT : 0 < T)
    (η : ℝ) (hη : η = Real.sqrt (2 * Real.log (Fintype.card A : ℝ) /
      (B ^ 2 * W ^ 2 * T)))
    {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (w wstar : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hwm : ∀ t < T, Measurable (w t))
    (hwstarm : ∀ t < T, Measurable (wstar t))
    (hwW : ∀ t < T, ∀ ω, ‖w t ω‖ ≤ W)
    (hwstar : ∀ t < T, ∀ ω,
      ‖wstar t ω‖ ≤ W ∧
        ∀ v, ‖v‖ ≤ W →
          qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
            (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν) ≤
          qLoss P r γ φ v (qnpgParams η w t ω)
            (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν))
    (εstat εbias : ℝ)
    (hstat : ∀ t < T,
      (∫ ω, (qLoss P r γ φ (w t ω) (qnpgParams η w t ω)
                (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν) -
              qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
                (onPolicyMeasure (logLinearPolicy φ (qnpgParams η w t ω)) P γ ν)) ∂ℙ) ≤ εstat)
    (hbias : ∀ t < T,
      (∫ ω, qLoss P r γ φ (wstar t ω) (qnpgParams η w t ω)
        (dstar P γ ρ πstar) ∂ℙ) ≤ εbias) :
    (∫ ω, (Finset.range T).inf' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hT))
      (fun t => PolicyGradTheory.ProjGA.valueAt πstar P r γ ρ -
        PolicyGradTheory.ProjGA.valueAt (logLinearPolicy φ (qnpgParams η w t ω)) P r γ ρ) ∂ℙ) ≤
      B * W / (1 - γ) * Real.sqrt (2 * Real.log (Fintype.card A : ℝ) / T) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * κ * εstat / (1 - γ) ^ 3) +
      Real.sqrt (4 * (Fintype.card A : ℝ) * εbias) / (1 - γ) := by sorry

end PolicyGradTheory.QNPG

