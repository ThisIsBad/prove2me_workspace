import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem

namespace SetCoverThreshold.SetCover

theorem lemma_2_3_1 (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode ℓ k code →
        (φ.toCNF.Satisfiable → ∃ A : φ.KStrategy ℓ k, ∀ r, φ.StrongAccept code A r) ∧
          (AtMostFracSat (1 - ε) φ.toCNF → ∀ A : φ.KStrategy ℓ k,
            φ.weakAcceptFrac code A ≤ (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ))) := by sorry

end SetCoverThreshold.SetCover
