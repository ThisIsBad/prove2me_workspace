import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

namespace FakeUserRanking.FORC

/-- Lemma 11, p. 51: one level `ℓ ≥ log₂ F` (Lean: `F ≤ 2^(k+1)`) is exposed to at most
`log(2L/δ) + 3` fake users with probability at least `1 − δ/(2L)`, for any `δ ∈ (0,1)`. -/
theorem lemma_11 (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (P : Adversary n) (hP : WithinBudget F P)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) :
    1 - δ / (2 * (numLevels T : ℝ)) ≤
      prob inst P (forc n T tb fb) T
        (fun τ => (exposure k τ : ℝ) ≤ Real.log (2 * (numLevels T : ℝ) / δ) + 3) := by sorry

end FakeUserRanking.FORC

