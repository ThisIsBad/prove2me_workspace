import Mathlib
import Definitions.Def_DLSConsensus_LowerBound_Model

namespace DLSConsensus.LowerBound

/-- Scenario C of the proof of Theorem 4.3 (p. 306). Let `π` be any protocol, `cm` a communication
model (Δ holds eventually with `Δ > 0`, or delta is unknown), `P`, `Q` a partition of the processors,
`RA` a run of Scenario A (initial values `0`, `Q` initially dead, `P → P` in time 1), `RB` a run of
Scenario B (initial values `1`, `P` initially dead, `Q → Q` in time 1), and `T` any time (in the proof,
`T = max(T_A, T_B)`). Then there is a run allowed by `cm` in which all processors take a step at every
tick (all alive), processors of `P` start with `0` and those of `Q` with `1`, messages from `P` to `P`
and from `Q` to `Q` are delivered in time 1, no message between the groups is delivered at a tick
`≤ T`, and every processor of `P` (resp. `Q`) is in the same state after each tick `n ≤ T` as in `RA`
(resp. `RB`). -/
theorem scenario_C {N : ℕ} {σ M : Type} (π : Protocol N σ M) (cm : Comm) (hcm : cm.WF)
    (P Q : Finset (Fin N)) (hdisj : Disjoint P Q) (hcover : P ∪ Q = Finset.univ)
    (RA RB : Run N σ) (hA : IsolatedScenario π P false RA) (hB : IsolatedScenario π Q true RB)
    (T : ℕ) :
    ∃ R : Run N σ, IsRun π R ∧ cm.Allowed π R ∧ FailStop Finset.univ R ∧
      (∀ i ∈ P, R.val i = false) ∧ (∀ i ∈ Q, R.val i = true) ∧
      TimeOneWithin π P R ∧ TimeOneWithin π Q R ∧
      (∀ k i s n, (k, s) ∈ R.deliv i n → (k ∈ P ↔ i ∈ Q) → T < n) ∧
      (∀ i ∈ P, ∀ n ≤ T, R.state i n = RA.state i n) ∧
      (∀ i ∈ Q, ∀ n ≤ T, R.state i n = RB.state i n) := by sorry

end DLSConsensus.LowerBound

