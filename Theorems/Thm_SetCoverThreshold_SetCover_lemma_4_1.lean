import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Reduction

namespace SetCoverThreshold.SetCover

theorem lemma_4_1 (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k m d : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode ℓ k code →
        ∀ P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d,
          (φ.toCNF.Satisfiable →
              ∃ 𝒞 : Finset (φ.SetIdx code), φ.IsSCCover code P 𝒞 ∧
                𝒞.card ≤ k * φ.numQuestions ℓ) ∧
            ∀ f : ℝ, 0 < f → (1 - f) * k * Real.log m ≤ d →
              (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ)) < 2 * (2 * f) / (k * Real.log m) ^ 2 →
                AtMostFracSat (1 - ε) φ.toCNF →
                  ∀ 𝒞 : Finset (φ.SetIdx code), φ.IsSCCover code P 𝒞 →
                    (1 - 2 * f) * k * φ.numQuestions ℓ * Real.log m ≤ 𝒞.card := by sorry

end SetCoverThreshold.SetCover
