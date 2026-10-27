import Mathlib
import Definitions.Def_CyberShare_Sharing_Model

namespace CyberShare.Sharing

/-- Lemma C.1, p. A.3 (PDF 35), with the printed sufficient bound (C.12), p. A.8 (PDF 40). -/
theorem lemma_c1 (a c gamma thL thH rho lam : ℝ)
    (h : BaseStanding a c gamma thL thH rho lam) :
    ∃ kappaBar : ℝ, 0 < kappaBar ∧ ∀ kappa : ℝ, kappaBar < kappa →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
        let P0 : Params := ⟨a, b, c, 0, gamma, kappa, thL, thH, rho, lam⟩
        0 < deltaLow P0 ∧ deltaLow P0 < a - c ∧
        ∀ delta : ℝ, deltaLow P0 < delta → delta < a - c →
          let P : Params := { P0 with delta := delta }
          ∀ s1 s2 : Dec,
            ∃ pair : (Sig → Sig → ℝ) × (Sig → Sig → ℝ),
              IsInvEq P s1 s2 pair.1 pair.2 ∧
              (∀ y y' : Sig, 0 < pair.1 y y' ∧ pair.1 y y' < delta / gamma ∧
                0 < pair.2 y y' ∧ pair.2 y y' < delta / gamma) ∧
              ∀ pair' : (Sig → Sig → ℝ) × (Sig → Sig → ℝ),
                IsInvEq P s1 s2 pair'.1 pair'.2 → pair' = pair := by sorry

end CyberShare.Sharing

