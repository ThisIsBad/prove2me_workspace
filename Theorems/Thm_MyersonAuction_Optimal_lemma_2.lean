import Definitions.Def_MyersonAuction_Optimal_Mechanism

noncomputable section

namespace MyersonAuction.Optimal

theorem lemma_2 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : Environment ι) (p x : Outcome ι) :
    Feasible E p x ↔
      WellDefined E p x ∧ ProbabilityCondition E p ∧
      MonotoneQ E p ∧ EnvelopeAndBaseIR E p x := by sorry

end MyersonAuction.Optimal

