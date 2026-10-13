import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model

namespace DLSConsensus.BasicRound

/-- Theorem 3.1 (p. 297): in the basic round model with omission (in particular fail-stop)
faults, if `N ≥ 2t + 1`, Algorithm 1 achieves consistency, strong unanimity and termination
for an arbitrary value domain `V`: for every set `C` of at least `N - t` correct processors,
every round `GST`, every message-loss pattern allowed by the model, every initial values and
every admissible choice of proposals. -/
theorem theorem_3_1 {N t : ℕ} (hN : 2 * t + 1 ≤ N) {V : Type*} (init : Fin N → V)
    (C : Finset (Fin N)) (hC : N - t ≤ C.card) (GST : ℕ) (deliv : ℕ → Fin N → Fin N → Prop)
    (hdeliv : DelivOK C GST deliv) (pick : ℕ → Set V → V) (hpick : PickAdmissible pick) :
    Consistency t pick init deliv C ∧ StrongUnanimity t pick init deliv C ∧
      Termination t pick init deliv C := by sorry

end DLSConsensus.BasicRound

