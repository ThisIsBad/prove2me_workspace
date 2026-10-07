import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_Procedure
import Definitions.Def_IgnallSchrage_Invariance_ThreeMachine
import Definitions.Def_IgnallSchrage_Invariance_TwoMachine

namespace IgnallSchrage.Invariance

/-- The THEOREM of the Appendix (p. 411). If the processing times of two flow-shop problems `P̃`
and `P'` are related by `ã_i = H (a'_i + G)`, `b̃_i = H (b'_i + G)`, `c̃_i = H (c'_i + G)` with
`H, G > 0` (processing times `a'_i, b'_i, c'_i ≥ 0`), then (1) the same sequences are optimal for both problems and (2) the
branch-and-bound procedure follows the same path for both, for the three-machine makespan problem
(with the lower bound of p. 401) and the two-machine sum-of-completion-times problem (with the
lower bound of p. 406). -/
theorem location_scale_invariance {n : ℕ} (a' b' c' : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a' i) (hb : ∀ i, 0 ≤ b' i) (hc : ∀ i, 0 ≤ c' i) (H G : ℝ)
    (hH : 0 < H) (hG : 0 < G) :
    (∀ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        IgnallSchrage.Makespan.makespan (shiftScale H G a') (shiftScale H G b') (shiftScale H G c') σ ≤
          IgnallSchrage.Makespan.makespan (shiftScale H G a') (shiftScale H G b') (shiftScale H G c') τ) ↔
      (∀ τ : Equiv.Perm (Fin n), IgnallSchrage.Makespan.makespan a' b' c' σ ≤ IgnallSchrage.Makespan.makespan a' b' c' τ)) ∧
    (∀ k : ℕ,
      IgnallSchrage.Makespan.run (lowerBound3 (shiftScale H G a') (shiftScale H G b') (shiftScale H G c')) k =
        IgnallSchrage.Makespan.run (lowerBound3 a' b' c') k) ∧
    (∀ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        sumCompletion (shiftScale H G a') (shiftScale H G b') σ ≤
          sumCompletion (shiftScale H G a') (shiftScale H G b') τ) ↔
      (∀ τ : Equiv.Perm (Fin n), sumCompletion a' b' σ ≤ sumCompletion a' b' τ)) ∧
    (∀ k : ℕ,
      IgnallSchrage.Makespan.run (lowerBound2 (shiftScale H G a') (shiftScale H G b')) k =
        IgnallSchrage.Makespan.run (lowerBound2 a' b') k) := by sorry

end IgnallSchrage.Invariance

