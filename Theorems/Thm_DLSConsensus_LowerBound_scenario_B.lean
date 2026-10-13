import Mathlib
import Definitions.Def_DLSConsensus_LowerBound_Model

namespace DLSConsensus.LowerBound

/-- Scenario B of the proof of Theorem 4.3 (p. 306), symmetric to Scenario A. Let `π` be a
`t`-resilient consensus protocol achieving weak unanimity in the communication model `cm`, and split
the processors into two disjoint groups `P`, `Q` with `1 ≤ |P|, |Q| ≤ t`. Scenario B — all initial
values `1` (`true`), the processors of `P` initially dead, messages from `Q` to `Q` delivered in
time 1 — has a run, and in every such run there is a finite `T_B` by which every processor of `Q` has
decided, and decided `1`. -/
theorem scenario_B {N : ℕ} {σ M : Type} (π : Protocol N σ M) (t : ℕ) (cm : Comm) (hcm : cm.WF)
    (htN : t ≤ N) (hres : Resilient π t cm) (P Q : Finset (Fin N)) (hdisj : Disjoint P Q)
    (hcover : P ∪ Q = Finset.univ) (hP1 : 1 ≤ P.card) (hPt : P.card ≤ t) (hQ1 : 1 ≤ Q.card)
    (hQt : Q.card ≤ t) :
    (∃ R : Run N σ, IsolatedScenario π Q true R) ∧
    ∀ R : Run N σ, IsolatedScenario π Q true R →
      ∃ TB : ℕ, ∀ i ∈ Q, ∃ n ≤ TB, DecidesAt π R i true n := by sorry

end DLSConsensus.LowerBound

