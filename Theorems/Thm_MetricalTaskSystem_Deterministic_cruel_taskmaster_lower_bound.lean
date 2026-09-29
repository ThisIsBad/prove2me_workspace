import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_CruelTaskmaster

namespace MetricalTaskSystem.Deterministic

/-- **Theorem 2.2** (Borodin–Linial–Saks 1992, p. 749). Let `A` be any on-line algorithm for a
metrical task system `(S, d)` with `n ≥ 2` states, and let `T(ε)` be the infinite task sequence
produced by the cruel taskmaster `M(ε)` in response to `A`. Then
`w_{T(ε)}(A) ≥ (2n − 1) / (1 + ε / min_{i ≠ j} d(i, j))`. -/
theorem cruel_taskmaster_lower_bound {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsMetrical d) (A : OnlineAlgorithm S) (s₀ : S)
    (ε : ℝ) (hε : 0 < ε) :
    ((((2 * (Fintype.card S : ℝ) - 1) / (1 + ε / minOffDiag d)) : ℝ) : EReal) ≤
      ratioLimsup d A s₀ (cruelSeq A s₀ ε) := by sorry

end MetricalTaskSystem.Deterministic

