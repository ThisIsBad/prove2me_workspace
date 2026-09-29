import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem
import Definitions.Def_SetCoverThreshold_MaxCover_Reduction

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-- **The gap of the §5 reduction** (Feige 1998, p. 649, proof of Theorem 5.3), from the cited
parallel repetition bound. (i) If `φ` is satisfiable, all `N` points of the §5 instance can be
covered by `kQ` sets. (ii) For every `ε > 0` there is `k₀` such that for every `k ≥ k₀` and
every `ε' > 0`, for all large enough `ℓ`: if at most a `(1 − ε')`-fraction of the clauses of
`φ` are simultaneously satisfiable, every collection of at most `kQ` sets covers at most
`(1 − 1/e + ε) N` points. -/
theorem gap_claim (hRaz : RazRepetition) :
    (∀ (k ℓ : ℕ) (code : Fin k → Fin ℓ → Bool) (φ : Formula5), φ.toCNF.Satisfiable →
        ∃ C : Finset (SetIdx φ code), C.card ≤ coverBudget φ code ∧
          coveredMaxCover φ code C = Finset.univ) ∧
      (∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
        ∀ code : Fin k → Fin ℓ → Bool, IsCode code →
          ∀ φ : Formula5, AtMostFracSat (1 - ε') φ.toCNF →
            ∀ C : Finset (SetIdx φ code), C.card ≤ coverBudget φ code →
              ((coveredMaxCover φ code C).card : ℝ) ≤
                (1 - Real.exp (-1) + ε) *
                  (Fintype.card (RandString φ ℓ × ((Fin ℓ → Bool) → Fin k)) : ℝ)) := by sorry

end SetCoverThreshold.MaxCover
