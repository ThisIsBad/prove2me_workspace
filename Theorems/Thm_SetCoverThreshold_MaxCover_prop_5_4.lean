import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

/-- **Proposition 5.4** (Feige 1998, p. 649): for every `ε > 0` and all large enough `k`, in
the §5 instance built from a 3CNF-5 formula `φ` and a code (weights `ℓ/2`, distances
`≥ ℓ/3`), every collection of at most `kQ` sets that covers at least a
`(1 − 1/e + ε)`-fraction of the `N` points has at least an `ε/3`-fraction of good random
strings. -/
theorem prop_5_4 (ε : ℝ) (hε : 0 < ε) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ (ℓ : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode code →
      ∀ (φ : Formula5) (C : Finset (SetIdx φ code)), C.card ≤ coverBudget φ code →
        (1 - Real.exp (-1) + ε) *
            (Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) : ℝ) ≤
          ((coveredMaxCover φ code C).card : ℝ) →
        ε / 3 * (Fintype.card (RandString φ ℓ) : ℝ) ≤ (goodCount φ code ε C : ℝ) := by sorry

end SetCoverThreshold.MaxCover
