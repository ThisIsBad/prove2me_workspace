import Mathlib
import Definitions.Def_LeviBalancing_TripleBalancing_Model
import Definitions.Def_LeviBalancing_TripleBalancing_Policy
import Definitions.Def_LeviBalancing_TripleBalancing_TBPolicy

open MeasureTheory ProbabilityTheory

namespace LeviBalancing.TripleBalancing

/-- §6.1, Rule 2 observation (p. 299): in a period in which the triple-balancing policy places an
order, no demand is left unsatisfied at the end of the period. -/
theorem no_backorders_after_order {Ω : Type*} [MeasurableSpace Ω] (M : LotSizingModel Ω)
    (I : ℕ → Kernel Ω (ℕ → ℝ)) (hI : M.IsCondDemandLaw I)
    (TB : ℕ → Ω → ℝ) (hTB : IsTripleBalancing M I TB) :
    ∀ s ∈ Finset.Icc 1 M.T, ∀ ω, 0 < TB s ω → M.D s ω ≤ levelAfter M TB s ω := by sorry

end LeviBalancing.TripleBalancing

