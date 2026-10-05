import Mathlib
import Definitions.Def_OnlineSetCover_LowerBound_Game
import Definitions.Def_OnlineSetCover_LowerBound_BlockFamily

namespace OnlineSetCover.LowerBound

/-- The adversary claim of §4 (Alon et al. 2009, p. 369): for positive integers `k, r` and every
valid deterministic online algorithm `A` for the block family on the `k r²` blocks of `2^k`
elements, there is a nonempty arrival sequence of at most `k r` elements that a single set of
the family covers (so `OPT = 1`), on which `A` chooses at least `k r` sets. -/
theorem block_adversary (k r : ℕ) (hk : 0 < k) (hr : 0 < r)
    (A : OnlineAlg (Fin (k * r ^ 2) × Fin (2 ^ k))) (hA : IsValid (blockFamily k r) A) :
    ∃ σ : List (Fin (k * r ^ 2) × Fin (2 ^ k)), σ ≠ [] ∧ σ.length ≤ k * r ∧
      (∃ S ∈ blockFamily k r, ∀ x ∈ σ, x ∈ S) ∧ k * r ≤ cost A σ := by sorry

end OnlineSetCover.LowerBound

