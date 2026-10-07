import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Lemma 3.3 (Payoff Equivalence), p.37:
`U_i(θ_i) = U_i(θ̲) + ∫_{θ̲}^{θ_i} Q_i(x) dx` in every incentive-compatible direct mechanism. -/
theorem payoff_equivalence {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) :
    ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
      m.interimU i x = m.interimU i E.lo + ∫ y in E.lo..x, m.interimQ i y := by sorry

end MechanismDesign.Auctions

