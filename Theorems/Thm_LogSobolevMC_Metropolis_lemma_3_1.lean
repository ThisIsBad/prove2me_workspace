import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Setting

namespace LogSobolevMC.Metropolis

/-- Lemma 3.1, p. 715: for any finite chain `K` with positive invariant probability `π`,
the log-Sobolev constant and the spectral gap satisfy `2α ≤ λ`. -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x) :
    2 * LogSobolevMC.ChiSquare.logSobolev K π ≤ LogSobolevMC.ChiSquare.gap K π := by sorry

end LogSobolevMC.Metropolis

