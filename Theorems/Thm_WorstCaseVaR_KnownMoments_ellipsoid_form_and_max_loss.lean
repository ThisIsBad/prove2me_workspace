import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- The ellipsoid form of Condition (10) (p. 546): with `Γ ≻ 0`,
`[[Γ, x - x̂], [(x - x̂)ᵀ, κ(ε)²]] ⪰ 0` iff `(x - x̂)ᵀ Γ⁻¹ (x - x̂) ≤ κ(ε)²`, and the maximal loss
`-xᵀw` over the `x` satisfying (10) is `κ(ε) √(wᵀΓw) - x̂ᵀw`. -/
theorem ellipsoid_form_and_max_loss {n : ℕ}
    (xhat w : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ x : EuclideanSpace ℝ (Fin n),
        (bordered Γ ⇑(x - xhat) (kappa ε ^ 2)).PosSemidef ↔
          ⇑(x - xhat) ⬝ᵥ Γ⁻¹ *ᵥ ⇑(x - xhat) ≤ kappa ε ^ 2) ∧
    IsGreatest {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin n),
        (bordered Γ ⇑(x - xhat) (kappa ε ^ 2)).PosSemidef ∧ r = -⟪x, w⟫_ℝ}
      (kappa ε * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ) := by sorry

end WorstCaseVaR.KnownMoments
