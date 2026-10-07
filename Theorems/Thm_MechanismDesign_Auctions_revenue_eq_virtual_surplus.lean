import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Eqs. (3.4)–(3.5), p.40: for an incentive-compatible direct mechanism whose payments satisfy
(3.3), i.e. `T_i(θ̲) = θ̲ Q_i(θ̲)` for all `i`, the seller's expected revenue equals
`∑_i ∫_{θ̲}^{θ̄} Q_i(θ_i) ψ_i(θ_i) f_i(θ_i) dθ_i = ∑_i ∫_Θ q_i(θ) ψ_i(θ_i) f(θ) dθ`. -/
theorem revenue_eq_virtual_surplus {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Environment ι}
    (m : DirectMechanism E) (hwd : m.WellDefined) (hIC : m.IsIC)
    (hlow : ∀ i, m.interimT i E.lo = E.lo * m.interimQ i E.lo) :
    m.revenue = ∑ i, ∫ x in E.lo..E.hi, m.interimQ i x * E.virtualValue i x * E.f i x ∧
    m.revenue = ∑ i, ∫ θ, m.q i θ * E.virtualValue i (θ i) ∂E.prior := by sorry

end MechanismDesign.Auctions

