import Mathlib

namespace ProcessingNetworks.FeedforwardStability

/-- A queueing network (Dai & Harrison, Section 2.6), restated from mission IV's
`QueueingNetworkData` (drafts in this series do not import one another): `I` buffers/classes
(one activity per buffer), `K` server pools. `p i` is the pool serving class `i`; `P` is the
`I × I` routing matrix, substochastic and transient (`Pⁿ → 0`, Section 2.6(iv)); `m` is the
vector of mean service times (`m > 0`, Assumption 2.1(b)); `lam` is the vector of external arrival
rates (`λ ≥ 0`); `b` is the `K`-vector of server-pool capacities (`b > 0`). -/
structure QueueingNetworkData (I K : ℕ) where
  p : Fin I → Fin K
  P : Matrix (Fin I) (Fin I) ℝ
  m : Fin I → ℝ
  lam : Fin I → ℝ
  b : Fin K → ℝ
  lam_nonneg : ∀ i, 0 ≤ lam i
  m_pos : ∀ i, 0 < m i
  b_pos : ∀ k, 0 < b k
  P_nonneg : ∀ i j, 0 ≤ P i j
  P_rowsum : ∀ i, ∑ j, P i j ≤ 1
  P_transient : ∀ i j, Filter.Tendsto (fun n => (P ^ n) i j) Filter.atTop (nhds 0)

/-- `I(k)` (Eq. (2.43)): the set of buffers/classes processed by server pool `k`. -/
def poolBuffers {I K : ℕ} (dat : QueueingNetworkData I K) (k : Fin K) : Finset (Fin I) :=
  Finset.univ.filter (fun i => dat.p i = k)

/-- The fluid equations (6.1)-(6.6), specialized to a queueing network, restated from mission
IV's `IsFluidModelSolutionQN` (see that mission's `MODERATION_NOTES.md` for the per-conjunct
correspondence): `B = 1` (identity consumption) and `Γ i j = P j i` (routing-induced output). -/
def IsFluidModelSolutionQN {I K : ℕ} (dat : QueueingNetworkData I K)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin I → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.P j i * Fh t j - Dh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = Fh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, dat.m i * Fh t i = Th t i) ∧
  (Th 0 = 0 ∧ Monotone Th) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k, ∑ i ∈ poolBuffers dat k, (Th t i - Th s i) ≤ dat.b k * (t - s))

end ProcessingNetworks.FeedforwardStability
