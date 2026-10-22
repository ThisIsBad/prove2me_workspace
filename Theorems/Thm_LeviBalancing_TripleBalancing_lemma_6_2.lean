import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model
import Definitions.Def_LeviBalancing_TripleBalancing_Policy
import Definitions.Def_LeviBalancing_TripleBalancing_TBPolicy

open MeasureTheory ProbabilityTheory

namespace LeviBalancing.TripleBalancing

/-- Lemma 6.2 (p. 300), stated for every feasible policy `P` in place of an optimal policy and in
additive form: `E[𝒞(TB)] ≤ E[𝒞(P)] + 2K · E[N]`. -/
theorem lemma_6_2 {Ω : Type*} [MeasurableSpace Ω] (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P) :
    expectedCost M TB ≤
      expectedCost M P + 2 * ENNReal.ofReal M.K * ∫⁻ ω, (numOrders M TB ω : ENNReal) ∂M.μ := by sorry

end LeviBalancing.TripleBalancing

