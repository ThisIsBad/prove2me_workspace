import Mathlib
import Definitions.Def_MechanismDesign_BilateralTrade_Model

open MeasureTheory

namespace MechanismDesign.BilateralTrade

/-- Proposition 3.14 (p.72), profit maximization. Assume `F_S`, `F_B` are regular, and let `m` be
a well-defined, incentive-compatible and individually rational direct mechanism. Sufficiency: if
(i) `q(θ) = 1` iff `ψ_B(θ_B) > ψ_S(θ_S)` for every `θ ∈ Θ` and (ii) the interim payments are
the incentive-compatible ones with binding participation of `θ̄_S` and `θ̲_B`, then `m`
maximizes the expected profit `E[t_B − t_S]` among all such mechanisms. Necessity: a maximizer
satisfies (ii), and (i) almost everywhere off the tie set `ψ_B(θ_B) = ψ_S(θ_S)` (under weak
regularity that set may have positive probability and the profit does not depend on `q` there). -/
theorem profit_maximization (E : Environment) (hreg : E.Regular) (m : DirectMechanism E)
    (hm : m.Admissible) :
    ((∀ m' : DirectMechanism E, m'.Admissible → m'.expectedSurplus ≤ m.expectedSurplus) →
      (∀ᵐ θ ∂E.prior, E.psiB θ.2 ≠ E.psiS θ.1 → m.q θ = profitRule E θ) ∧
      (∀ y ∈ Set.Icc E.loB E.hiB, m.TB y = y * m.QB y - ∫ z in E.loB..y, m.QB z) ∧
      (∀ x ∈ Set.Icc E.loS E.hiS,
        m.TS x = E.hiS - (1 - m.QS x) * x - ∫ z in x..E.hiS, (1 - m.QS z))) ∧
    ((∀ θ ∈ E.typeSpace, m.q θ = profitRule E θ) →
      (∀ y ∈ Set.Icc E.loB E.hiB, m.TB y = y * m.QB y - ∫ z in E.loB..y, m.QB z) →
      (∀ x ∈ Set.Icc E.loS E.hiS,
        m.TS x = E.hiS - (1 - m.QS x) * x - ∫ z in x..E.hiS, (1 - m.QS z)) →
      ∀ m' : DirectMechanism E, m'.Admissible → m'.expectedSurplus ≤ m.expectedSurplus) := by sorry

end MechanismDesign.BilateralTrade

