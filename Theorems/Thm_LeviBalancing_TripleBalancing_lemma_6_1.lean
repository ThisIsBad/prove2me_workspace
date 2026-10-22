import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model
import Definitions.Def_LeviBalancing_TripleBalancing_Policy
import Definitions.Def_LeviBalancing_TripleBalancing_TBPolicy

open MeasureTheory ProbabilityTheory

namespace LeviBalancing.TripleBalancing

/-- Lemma 6.1 (p. 300), stated for every feasible policy `P` in place of an optimal policy:
`E[𝒞(P)] ≥ K · E[N]`, where `N` is the number of orders of the triple-balancing policy. -/
theorem lemma_6_1 {Ω : Type*} [MeasurableSpace Ω] (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB)
    (P : ℕ → Ω → ℝ) (hP : IsFeasiblePolicy M P) :
    ENNReal.ofReal M.K * ∫⁻ ω, (numOrders M TB ω : ENNReal) ∂M.μ ≤ expectedCost M P := by sorry

end LeviBalancing.TripleBalancing

