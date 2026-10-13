import Mathlib
import Definitions.Def_SennottDP_AvgASM_Criteria
import Definitions.Def_SennottDP_AvgASM_ServiceQueue

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.AvgASM

/-- **Proposition 8.5.1** (Sennott 1999, p. 182). In the single-server queue with service rate
control and Bernoulli(`p`) arrivals, holding cost `H(i) = H i` and service cost `C(a)`, let the
allowable rate `a` satisfy `p < a`, and let `d(a)` be the policy that always serves at rate `a`.
Then, from every initial state `i`,
`J_{d(a)} = H p (1 − p)/(a − p) + p C(a)/a` (8.12). -/
theorem service_queue_open_loop_cost (Q : ServiceQueueData) (a : ℝ) (ha : a ∈ Q.rates)
    (hpa : Q.p < a) (i : ℕ) :
    avgCost (Q.serveAt a ha).toPolicy i =
      ENNReal.ofReal ((Q.H : ℝ) * Q.p * (1 - Q.p) / (a - Q.p) + Q.p * (Q.serviceCost a : ℝ) / a) := by sorry

end SennottDP.AvgASM

