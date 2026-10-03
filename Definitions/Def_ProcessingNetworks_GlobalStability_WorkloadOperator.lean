import Mathlib
import Definitions.Def_ProcessingNetworks_GlobalStability_QueueingNetworkData

namespace ProcessingNetworks.GlobalStability

open Matrix

/-- The workload operator `W : ℝ^I_+ → ℝ^K_+`, Eq. (8.24), restated from mission VI's
`workloadOperator`: `W(z) := AM(I-P')⁻¹z`. `Q` stands for `(I-P')⁻¹`, supplied as data with its
defining two-sided-inverse property. -/
def workloadOperator {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (z : Fin I → ℝ) (k : Fin K) : ℝ :=
  ∑ i ∈ poolBuffers dat k, dat.m i * (Q.mulVec z) i

/-- `α`, the vector of total arrival rates (Eq. 2.38), the unique solution of the traffic
equations `α = λ + P'α` (Eq. 2.36), i.e. `α := Qλ`. -/
def totalArrivalRates {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ) :
    Fin I → ℝ :=
  Q.mulVec dat.lam

/-- `Q` genuinely represents the routing-matrix inverse `(I - P')⁻¹`. -/
def IsRoutingInverse {I : ℕ} (P : Matrix (Fin I) (Fin I) ℝ) (Q : Matrix (Fin I) (Fin I) ℝ) : Prop :=
  Q * (1 - Pᵀ) = 1 ∧ (1 - Pᵀ) * Q = 1

end ProcessingNetworks.GlobalStability
