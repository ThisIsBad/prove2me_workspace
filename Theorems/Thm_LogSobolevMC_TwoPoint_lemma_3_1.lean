import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing

/-- Lemma 3.1 (p. 715): for any finite chain `K` with positive invariant probability `π`,
the log-Sobolev constant `α` and the spectral gap `λ` satisfy `2α ≤ λ`. -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) :
    2 * LogSobolevMC.ChiSquare.logSobolev K π ≤ LogSobolevMC.ChiSquare.gap K π := by sorry

end LogSobolevMC.TwoPoint

