import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Proposition 3.2, p.38: a direct mechanism is incentive-compatible if and only if, for
every buyer `i`, `Q_i` is increasing on `[θ̲, θ̄]` and
`T_i(θ_i) = T_i(θ̲) + (θ_i Q_i(θ_i) − θ̲ Q_i(θ̲)) − ∫_{θ̲}^{θ_i} Q_i(x) dx` for every `θ_i`. -/
theorem ic_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) :
    m.IsIC ↔ ∀ i, MonotoneOn (m.interimQ i) (Set.Icc E.lo E.hi) ∧
      ∀ x ∈ Set.Icc E.lo E.hi,
        m.interimT i x = m.interimT i E.lo + (x * m.interimQ i x - E.lo * m.interimQ i E.lo)
          - ∫ y in E.lo..x, m.interimQ i y := by sorry

end MechanismDesign.Auctions

