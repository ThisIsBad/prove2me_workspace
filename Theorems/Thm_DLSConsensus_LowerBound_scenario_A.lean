import Mathlib
import Definitions.Def_DLSConsensus_LowerBound_Model

namespace DLSConsensus.LowerBound

/-- Scenario A of the proof of Theorem 4.3 (p. 305). Let `π` be a `t`-resilient consensus protocol
achieving weak unanimity in the communication model `cm` (Δ holds eventually, with `Δ > 0`, or delta
is unknown), and split the processors into two disjoint groups `P`, `Q` with `1 ≤ |P|, |Q| ≤ t`.
Scenario A — all initial values `0` (`false`), the processors of `Q` initially dead, messages from `P`
to `P` delivered in time 1 — has a run, and in every such run there is a time `T_A` by which every
processor of `P` has decided, and decided `0`. -/
theorem scenario_A {N : ℕ} {σ M : Type} (π : Protocol N σ M) (t : ℕ) (cm : Comm) (hcm : cm.WF)
    (htN : t ≤ N) (hres : Resilient π t cm) (P Q : Finset (Fin N)) (hdisj : Disjoint P Q)
    (hcover : P ∪ Q = Finset.univ) (hP1 : 1 ≤ P.card) (hPt : P.card ≤ t) (hQ1 : 1 ≤ Q.card)
    (hQt : Q.card ≤ t) :
    (∃ R : Run N σ, IsolatedScenario π P false R) ∧
    ∀ R : Run N σ, IsolatedScenario π P false R →
      ∃ TA : ℕ, ∀ i ∈ P, ∃ n ≤ TA, DecidesAt π R i false n := by sorry

end DLSConsensus.LowerBound

