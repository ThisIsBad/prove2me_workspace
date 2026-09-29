import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SetCoverThreshold_MaxCover_Formula
import Definitions.Def_SetCoverThreshold_MaxCover_ProofSystem

namespace SetCoverThreshold.MaxCover

open CookPvsNP

/-- **Lemma 2.3.1** (Feige 1998, p. 643), from the cited parallel repetition bound: for every
`ε > 0` there is `c > 0` such that for every 3CNF-5 formula `φ`, every `ℓ`, `k` and every
code of `k` words of length `ℓ`, weight `ℓ/2` and pairwise distance `≥ ℓ/3`: if `φ` is
satisfiable the provers can make the verifier always strongly accept, and if at most a
`(1 − ε)`-fraction of its clauses are simultaneously satisfiable, the verifier weakly accepts
with probability at most `k^2 · 2^{−cℓ}` under every strategy. -/
theorem lemma_2_3_1 (hRaz : RazRepetition) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φ : Formula5) (ℓ k : ℕ) (code : Fin k → Fin ℓ → Bool), IsCode code →
        (φ.toCNF.Satisfiable →
            ∃ strat : Fin k → Strategy φ ℓ, ∀ r, StrongAccept φ code strat r) ∧
        (AtMostFracSat (1 - ε) φ.toCNF →
            ∀ strat : Fin k → Strategy φ ℓ,
              weakAcceptFrac φ code strat ≤ (k : ℝ) ^ 2 * (2 : ℝ) ^ (-(c * ℓ))) := by sorry

end SetCoverThreshold.MaxCover
