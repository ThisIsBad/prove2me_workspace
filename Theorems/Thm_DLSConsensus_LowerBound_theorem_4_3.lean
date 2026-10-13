import Mathlib
import Definitions.Def_DLSConsensus_LowerBound_Model

namespace DLSConsensus.LowerBound

/-- Theorem 4.3 (Dwork, Lynch, Stockmeyer 1988, p. 305), fail-stop case: with synchronous processors
(Φ = 1) and partially synchronous communication — (a) Δ holds eventually, for every positive Δ, or
(b) delta is unknown — and `2 ≤ N ≤ 2t` (with the standing `t ≤ N` of §2.4), no protocol for binary
values is a `t`-resilient consensus protocol achieving weak unanimity. The state and message types
of the protocol are arbitrary (possibly infinite). -/
theorem theorem_4_3 (N t : ℕ) (hN : 2 ≤ N) (hNt : N ≤ 2 * t) (htN : t ≤ N) :
    (∀ Δ : ℕ, 0 < Δ → ∀ (σ M : Type) (π : Protocol N σ M),
      ¬ Resilient π t (Comm.eventually Δ)) ∧
    (∀ (σ M : Type) (π : Protocol N σ M), ¬ Resilient π t Comm.unknown) := by sorry

end DLSConsensus.LowerBound

