import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Proposition 3.3, p.39: an incentive-compatible direct mechanism is individually rational
if and only if `T_i(θ̲) ≤ θ̲ Q_i(θ̲)` for every buyer `i`. -/
theorem ir_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hIC : m.IsIC) :
    m.IsIR ↔ ∀ i, m.interimT i E.lo ≤ E.lo * m.interimQ i E.lo := by sorry

end MechanismDesign.Auctions

