import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Lemma 3.1, p.37: in an incentive-compatible direct mechanism every interim allocation
probability `Q_i` is (weakly) increasing on `[θ̲, θ̄]`. -/
theorem interimQ_monotone {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) (i : ι) :
    MonotoneOn (m.interimQ i) (Set.Icc E.lo E.hi) := by sorry

end MechanismDesign.Auctions

