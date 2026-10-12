import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

namespace PoissonDepTrials.SecondOrder

/-- (5.8), proof of Theorem 5.1, p. 544, in index form: for independent Bernoulli trials,
`Eh(W) = 𝒫_λh − Σ_{i=1}^n p_i² E U_λh(W^{(i)})`. -/
theorem identity_5_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (X : ℕ → Ω → ℕ) (hX : IsBernoulliTrials P n X) (hind : iIndepFun (fun i => X i) P)
    (hlam : 0 < lam P n X) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∫ ω, h (W n X ω) ∂P = poissonExp (lam P n X) h -
      ∑ i ∈ Finset.Icc 1 n, prob P X i ^ 2 * ∫ ω, stU (lam P n X) h (Wi n X i ω) ∂P := by sorry

end PoissonDepTrials.SecondOrder

