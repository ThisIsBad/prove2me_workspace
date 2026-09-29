import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Formula
import Definitions.Def_SetCoverThreshold_SetCover_ProofSystem
import Definitions.Def_SetCoverThreshold_SetCover_Reduction

namespace SetCoverThreshold.SetCover

theorem prop_4_2 (φ : Formula5) (ℓ k m : ℕ) (code : Fin k → Fin ℓ → Bool)
    (hcode : IsCode ℓ k code) (hk : 0 < k) (hm : 2 ≤ m)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒞 : Finset (φ.SetIdx code))
    (h𝒞 : (𝒞.card : ℝ) ≤ (1 - δ) * k * φ.numQuestions ℓ * Real.log m) :
    δ / 2 ≤
      ((Finset.univ.filter (fun r : φ.RandomString ℓ =>
          (φ.weight code 𝒞 r : ℝ) < (1 - δ / 2) * k * Real.log m)).card : ℝ) /
        Fintype.card (φ.RandomString ℓ) := by sorry

end SetCoverThreshold.SetCover
