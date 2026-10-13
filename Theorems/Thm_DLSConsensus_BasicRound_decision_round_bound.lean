import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model

namespace DLSConsensus.BasicRound

/-- Section 3.2.1, p. 298: under the hypotheses of Theorem 3.1, every processor in `C` decides at
some phase `k` whose decision round `4k - 1` is at most `GST + 4(N + 1)`. -/
theorem decision_round_bound {N t : ℕ} (hN : 2 * t + 1 ≤ N) {V : Type*} (init : Fin N → V)
    (C : Finset (Fin N)) (hC : N - t ≤ C.card) (GST : ℕ) (deliv : ℕ → Fin N → Fin N → Prop)
    (hdeliv : DelivOK C GST deliv) (pick : ℕ → Set V → V) (hpick : PickAdmissible pick) :
    ∀ p ∈ C, ∃ (k : ℕ) (v : V),
      DecidesAt t pick init deliv p k v ∧ 4 * k - 1 ≤ GST + 4 * (N + 1) := by sorry

end DLSConsensus.BasicRound

