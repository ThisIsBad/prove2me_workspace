import Mathlib
import Definitions.Def_MechanismDesign_Auctions_Model

open MeasureTheory

namespace MechanismDesign.Auctions

/-- Proposition 3.5, p.42: an incentive-compatible, individually rational direct mechanism that
allocates efficiently (`q_i(θ) = 1` if `θ_i > θ_j` for all `j ≠ i`, else `0`) and satisfies
`T_i(θ_i) ≤ θ_i Q_i(θ_i) − ∫_{θ̲}^{θ_i} Q_i(x) dx` exists; and among all incentive-compatible,
individually rational direct mechanisms, a mechanism maximizes expected welfare
`E[∑_i q_i(θ) θ_i]` if and only if it allocates efficiently for almost every `θ` and satisfies
the payment inequality for every `θ_i`. (The page says "for all `θ ∈ Θ`"; ties `θ_i = θ_j` are a
null event, so the characterization holds almost everywhere.) -/
theorem welfare_maximization {ι : Type*} [Fintype ι] [DecidableEq ι] (E : Environment ι) :
    (∃ m : DirectMechanism E, m.Admissible ∧
      (∀ i, ∀ θ ∈ E.typeSpace, m.q i θ = efficientAlloc i θ) ∧
      ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
        m.interimT i x ≤ x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y) ∧
    ∀ m : DirectMechanism E, m.Admissible →
      ((∀ m' : DirectMechanism E, m'.Admissible → m'.welfare ≤ m.welfare) ↔
        ((∀ i, ∀ᵐ θ ∂E.prior, m.q i θ = efficientAlloc i θ) ∧
          ∀ i, ∀ x ∈ Set.Icc E.lo E.hi,
            m.interimT i x ≤ x * m.interimQ i x - ∫ y in E.lo..x, m.interimQ i y)) := by sorry

end MechanismDesign.Auctions

