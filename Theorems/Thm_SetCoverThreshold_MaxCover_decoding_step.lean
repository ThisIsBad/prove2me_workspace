import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

/-- **Decoding step** (Feige 1998, p. 649, proof of Theorem 5.3): if at least an `ε/3`-fraction
of the random strings are good for a collection `C` of sets of the §5 instance, then some
strategy of the `k` provers makes the verifier weakly accept with probability at least
`(ε/3) · (ε/(3k))^2`. -/
theorem decoding_step (ε : ℝ) (hε : 0 < ε) (k ℓ : ℕ) (code : Fin k → Fin ℓ → Bool)
    (φ : Formula5) (C : Finset (SetIdx φ code))
    (hgood : ε / 3 * (Fintype.card (RandString φ ℓ) : ℝ) ≤ (goodCount φ code ε C : ℝ)) :
    ∃ strat : Fin k → Strategy φ ℓ,
      ε / 3 * (ε / (3 * k)) ^ 2 * (Fintype.card (RandString φ ℓ) : ℝ) ≤
        (weakAcceptCount φ code strat : ℝ) := by sorry

end SetCoverThreshold.MaxCover
