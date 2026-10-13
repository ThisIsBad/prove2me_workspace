import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model

namespace DLSConsensus.BasicRound

/-- Lemma 3.1 (p. 296): it is impossible for two distinct values to acquire locks with the same
associated phase. If processor `p` locks `v` at phase `k` and processor `q` locks `w` at the
same phase `k`, then `v = w`. -/
theorem lemma_3_1 {N : ℕ} {V : Type*} (t : ℕ) (pick : ℕ → Set V → V) (init : Fin N → V)
    (deliv : ℕ → Fin N → Fin N → Prop) (k : ℕ) (p q : Fin N) (v w : V)
    (hp : LocksAt t pick init deliv p k v) (hq : LocksAt t pick init deliv q k w) :
    v = w := by sorry

end DLSConsensus.BasicRound

