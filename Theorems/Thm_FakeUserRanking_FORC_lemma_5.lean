import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

/-- Lemma 5 (Effective Fakeness Budget for High Learning Levels), p. 25. -/
theorem lemma_5 (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)) :
    1 - delta n T / 2 ≤
      prob inst P (forc n T tb fb) T
        (fun τ => ∀ k : Fin (numLevels T), F ≤ 2 ^ ((k : ℕ) + 1) →
          (exposure k τ : ℝ) ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) + 3) := by sorry

end FakeUserRanking.FORC

