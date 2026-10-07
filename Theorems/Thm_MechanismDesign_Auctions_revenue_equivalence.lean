import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Lemma 3.4 (Revenue Equivalence), p.37:
`T_i(θ_i) = T_i(θ̲) + (θ_i Q_i(θ_i) − θ̲ Q_i(θ̲)) − ∫_{θ̲}^{θ_i} Q_i(x) dx` in every
incentive-compatible direct mechanism. -/
theorem revenue_equivalence {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) :
    ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
      m.interimT i x = m.interimT i E.lo + (x * m.interimQ i x - E.lo * m.interimQ i E.lo)
        - ∫ y in E.lo..x, m.interimQ i y := by sorry

end MechanismDesign.Auctions

