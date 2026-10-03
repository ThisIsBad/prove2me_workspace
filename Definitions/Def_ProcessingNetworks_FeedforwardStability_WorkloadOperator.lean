import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData

namespace ProcessingNetworks.FeedforwardStability

open Matrix

/-- The workload operator `W : ℝ^I_+ → ℝ^K_+`, Eq. (8.24): `W(z) := AM(I-P')⁻¹z`, where `A` is
the `0`-`1` capacity-consumption matrix (`A k i = 1 ↔ p(i) = k`, so `(AMx)_k = ∑_{i∈I(k)} m_i xᵢ`)
and `M = diag(m)`. `Q` stands for the routing-matrix inverse `(I-P')⁻¹`, supplied as data with
its defining two-sided-inverse property rather than computed, matching how the book treats it
(via the Neumann expansion (2.37), assuming `P` substochastic and transient). -/
def workloadOperator {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (z : Fin I → ℝ) (k : Fin K) : ℝ :=
  ∑ i ∈ poolBuffers dat k, dat.m i * (Q.mulVec z) i

/-- `α`, the vector of total arrival rates (Eq. 2.38), the unique solution of the traffic
equations `α = λ + P'α` (Eq. 2.36), i.e. `α := Qλ` for `Q = (I-P')⁻¹`. -/
def totalArrivalRates {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ) :
    Fin I → ℝ :=
  Q.mulVec dat.lam

/-- `Q` genuinely represents the routing-matrix inverse `(I - P')⁻¹` (a two-sided inverse of
`1 - Pᵀ`). -/
def IsRoutingInverse {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (Q : Matrix (Fin I) (Fin I) ℝ) : Prop :=
  Q * (1 - Pᵀ) = 1 ∧ (1 - Pᵀ) * Q = 1

end ProcessingNetworks.FeedforwardStability
