import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- The inner value `φ(y)` of the dual problem (p. 547) and its maximum over `y ∈ [ε, 1]`:
(a) for `0 < y < 1`, the maximum of `-vᵀw / y` over `v` with
`Γ ⪰ (1/(y(1-y)))(v - yx̂)(v - yx̂)ᵀ` is `φ(y) = √((1-y)/y) √(wᵀΓw) - x̂ᵀw`;
(b) the maximum of `φ` over `[ε, 1]` is `κ(ε) √(wᵀΓw) - x̂ᵀw`. -/
theorem phi_closed_form_and_maximum {n : ℕ}
    (xhat w : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ y : ℝ, 0 < y → y < 1 →
      IsGreatest {r : ℝ | ∃ v : EuclideanSpace ℝ (Fin n),
          (Γ - (1 / (y * (1 - y))) • vecMulVec ⇑(v - y • xhat) ⇑(v - y • xhat)).PosSemidef ∧
          r = -⟪v, w⟫_ℝ / y}
        (Real.sqrt ((1 - y) / y) * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ)) ∧
    IsGreatest
      ((fun y : ℝ => Real.sqrt ((1 - y) / y) * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ) ''
        Set.Icc ε 1)
      (kappa ε * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ) := by sorry

end WorstCaseVaR.KnownMoments
