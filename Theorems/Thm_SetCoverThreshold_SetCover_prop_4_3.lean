import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
import Definitions.Def_SetCoverThreshold_SetCover_Reduction

namespace SetCoverThreshold.SetCover

theorem prop_4_3 (φ : Formula5) (ℓ k m d : ℕ) (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode ℓ k code) (P : φ.RandomString ℓ → PartitionSystem m (2 ^ ℓ) k d)
    (δ : ℝ) (hδ : 0 < δ) (hd : (1 - δ / 2) * k * Real.log m ≤ d)
    (𝒞 : Finset (φ.SetIdx code)) (hcov : φ.IsSCCover code P 𝒞)
    (h𝒞 : (𝒞.card : ℝ) ≤ (1 - δ) * k * φ.numQuestions ℓ * Real.log m) :
    ∃ A : φ.KStrategy ℓ k, 2 * δ / (k * Real.log m) ^ 2 ≤ φ.weakAcceptFrac code A := by sorry

end SetCoverThreshold.SetCover
