import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 2, pp. 12–13 (carrier axiom): for `S, T ∈ N/g`,
`∑_{i ∈ S} φ_i(u^T) = u^T_N` if `S = T`, and `= 0` if `S ∩ T = ∅` (distinct components are
disjoint). -/
theorem carrier_identity {n : ℕ} (hn : 0 < n) (v : Game n) (g : SimpleGraph (Fin n))
    (S T : Finset (Fin n)) (hS : S ∈ quot univ g) (hT : T ∈ quot univ g) :
    ∑ i ∈ S, shapley (uGame v g T) i = if S = T then uGame v g T univ else 0 := by sorry

end CooperationGraphs.FairRule

