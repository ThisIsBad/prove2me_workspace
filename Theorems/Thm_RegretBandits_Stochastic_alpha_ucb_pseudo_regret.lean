import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_RegretBandits_Stochastic_model
import Definitions.Def_RegretBandits_Stochastic_alphaPsiUCB

namespace RegretBandits.Stochastic

open MeasureTheory ImprovedLinBandits.UCBDelta

/-- Eq. (2.4) of Bubeck and Cesa-Bianchi (arXiv:1204.5721v2, p. 11): for `[0, 1]`-valued rewards,
α-UCB, i.e. (α, ψ)-UCB with `ψ(λ) = λ²/8` (Hoeffding's lemma, `ψ*(ε) = 2ε²`) and `α > 2`, satisfies
`R̄_n ≤ ∑_{i : Δ_i > 0} ((2α/Δ_i) ln n + α/(α - 2))`. -/
theorem alpha_ucb_pseudo_regret {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {K : ℕ} (hK : 2 ≤ K) (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ)
    (hX : IsStochasticBandit P X μ)
    (hbdd : ∀ i k, ∀ᵐ ω ∂P, X i k ω ∈ Set.Icc (0 : ℝ) 1)
    (α : ℝ) (hα : 2 < α) (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t))
    (hrun : IsAlphaPsiUCBRun (fun l => l ^ 2 / 8) α X I) (n : ℕ) :
    pseudoRegretBar P μ I n ≤
      ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
        (2 * α / gap μ i * Real.log (n : ℝ) + α / (α - 2)) := by sorry

end RegretBandits.Stochastic

