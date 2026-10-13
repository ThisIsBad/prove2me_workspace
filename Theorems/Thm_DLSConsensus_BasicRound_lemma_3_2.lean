import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model

namespace DLSConsensus.BasicRound

/-- Lemma 3.2 (p. 297): if some processor (correct or not) decides `v` at phase `k`, and no
processor decides anything at a phase `< k`, then at least `t + 1` processors lock `v` at
phase `k`, and each processor that locks `v` at phase `k` has, after every round
`r ≥ 4k - 2`, a lock on `v` with associated phase at least `k`. -/
theorem lemma_3_2 {N : ℕ} {V : Type*} (t : ℕ) (ht : t ≤ N) (pick : ℕ → Set V → V)
    (hpick : PickAdmissible pick) (init : Fin N → V) (deliv : ℕ → Fin N → Fin N → Prop)
    (p : Fin N) (k : ℕ) (v : V) (hdec : DecidesAt t pick init deliv p k v)
    (hmin : ∀ k' < k, ∀ (q : Fin N) (w : V), ¬ DecidesAt t pick init deliv q k' w) :
    t + 1 ≤ (Lockers t pick init deliv k v).card ∧
      ∀ q : Fin N, LocksAt t pick init deliv q k v →
        ∀ r : ℕ, 4 * k - 2 ≤ r →
          ∃ h : ℕ, k ≤ h ∧ (exec t pick init deliv r q).lock v = some h := by sorry

end DLSConsensus.BasicRound

