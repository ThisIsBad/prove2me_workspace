import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Proposition 3.4 (Myerson, 1981), p.41. Under regularity (Assumption 3.1) there is an
incentive-compatible, individually rational direct mechanism with Myerson's allocation rule
(i) and the payments (ii) `T_i(θ_i) = θ_i Q_i(θ_i) − ∫_{θ̲}^{θ_i} Q_i(x) dx`; and among all
incentive-compatible, individually rational direct mechanisms, a mechanism maximizes the
seller's expected revenue if and only if its allocation rule agrees with (i) for almost every
`θ` and its interim payments satisfy (ii) for every `θ_i`. (The page says "for all `θ ∈ Θ`";
ties `ψ_i(θ_i) = ψ_j(θ_j)` are a null event, so the characterization holds almost everywhere.) -/
theorem myerson_optimal_auction {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Environment ι)
    (hreg : E.Regular) :
    (∃ m : DirectMechanism E, m.Admissible ∧
      (∀ i, ∀ θ ∈ E.typeSpace, m.q i θ = E.myersonAlloc i θ) ∧
      ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
        m.interimT i x = x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y) ∧
    ∀ m : DirectMechanism E, m.Admissible →
      ((∀ m' : DirectMechanism E, m'.Admissible → m'.revenue ≤ m.revenue) ↔
        ((∀ i, ∀ᵐ θ ∂E.prior, m.q i θ = E.myersonAlloc i θ) ∧
          ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
            m.interimT i x = x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y)) := by sorry

end MechanismDesign.Auctions

