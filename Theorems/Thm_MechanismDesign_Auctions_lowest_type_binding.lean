import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Lemma 3.5, p.39: if an incentive-compatible, individually rational direct mechanism
maximizes the seller's expected revenue among all such mechanisms, then
`T_i(θ̲) = θ̲ Q_i(θ̲)` for every buyer `i`. -/
theorem lowest_type_binding {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hm : m.Admissible)
    (hopt : ∀ m' : DirectMechanism E, m'.Admissible → m'.revenue ≤ m.revenue) :
    ∀ i, m.interimT i E.lo = E.lo * m.interimQ i E.lo := by sorry

end MechanismDesign.Auctions

