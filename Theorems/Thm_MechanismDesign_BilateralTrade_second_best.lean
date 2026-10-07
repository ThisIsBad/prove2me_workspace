import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Proposition 3.13 (p.71), second best. Assume `θ̲_B < θ̄_S`, `θ̄_B > θ̲_S` and that `F_S`,
`F_B` are regular. A direct mechanism is well-defined, incentive-compatible, individually rational,
ex ante budget balanced and maximizes expected welfare among all such mechanisms if and only if
(i) its trading rule is the rule (3.70) for some `λ > 0`, (ii) exact budget balance holds, and
(iii) the interim payments are the incentive-compatible ones with binding participation of
`θ̄_S` and `θ̲_B`. Necessity of (i) is stated almost everywhere (the page's "for all `θ ∈ Θ`" is
false on null sets); sufficiency assumes (i) on all of `Θ`. -/
theorem second_best (E : Environment) (hB : E.loB < E.hiS) (hS : E.loS < E.hiB)
    (hreg : E.Regular) (m : DirectMechanism E) :
    ((m.Admissible ∧ m.ExAnteBB ∧
        ∀ m' : DirectMechanism E, m'.Admissible → m'.ExAnteBB → m'.welfare ≤ m.welfare) →
      (∃ lam : ℝ, 0 < lam ∧ ∀ᵐ θ ∂E.prior, m.q θ = lambdaRule E lam θ) ∧
      (∫ θ, m.q θ * (E.psiB θ.2 - E.psiS θ.1) ∂E.prior = E.hiS - ∫ θ, E.psiS θ.1 ∂E.prior) ∧
      (∀ y ∈ Set.Icc E.loB E.hiB, m.TB y = y * m.QB y - ∫ z in E.loB..y, m.QB z) ∧
      (∀ x ∈ Set.Icc E.loS E.hiS,
        m.TS x = E.hiS - (1 - m.QS x) * x - ∫ z in x..E.hiS, (1 - m.QS z))) ∧
    (m.WellDefined →
      (∃ lam : ℝ, 0 < lam ∧ ∀ θ ∈ E.typeSpace, m.q θ = lambdaRule E lam θ) →
      (∫ θ, m.q θ * (E.psiB θ.2 - E.psiS θ.1) ∂E.prior = E.hiS - ∫ θ, E.psiS θ.1 ∂E.prior) →
      (∀ y ∈ Set.Icc E.loB E.hiB, m.TB y = y * m.QB y - ∫ z in E.loB..y, m.QB z) →
      (∀ x ∈ Set.Icc E.loS E.hiS,
        m.TS x = E.hiS - (1 - m.QS x) * x - ∫ z in x..E.hiS, (1 - m.QS z)) →
      m.Admissible ∧ m.ExAnteBB ∧
        ∀ m' : DirectMechanism E, m'.Admissible → m'.ExAnteBB → m'.welfare ≤ m.welfare) := by sorry

end MechanismDesign.BilateralTrade

