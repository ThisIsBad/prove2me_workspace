import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Setting

namespace LogSobolevMC.Metropolis

/-- Lemma 3.3, p. 718: if two chains `(K, π)`, `(K', π')` on the same finite set satisfy
`ℰ' ≤ Aℰ` and `aπ ≤ π'` with `A, a > 0`, then `λ' ≤ (A/a)λ` and `α' ≤ (A/a)α`. -/
theorem lemma_3_3 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (K' : Matrix V V ℝ) (hK' : MarkovMixing.IsStochastic K')
    (π' : V → ℝ) (hπ' : MarkovMixing.IsStationary K' π') (hπ'pos : ∀ x, 0 < π' x)
    (A a : ℝ) (hA : 0 < A) (ha : 0 < a)
    (hE : ∀ f : V → ℝ, LogSobolevMC.ChiSquare.dirichlet K' π' f f ≤ A * LogSobolevMC.ChiSquare.dirichlet K π f f)
    (hmeas : ∀ x, a * π x ≤ π' x) :
    LogSobolevMC.ChiSquare.gap K' π' ≤ A / a * LogSobolevMC.ChiSquare.gap K π ∧ LogSobolevMC.ChiSquare.logSobolev K' π' ≤ A / a * LogSobolevMC.ChiSquare.logSobolev K π := by sorry

end LogSobolevMC.Metropolis

