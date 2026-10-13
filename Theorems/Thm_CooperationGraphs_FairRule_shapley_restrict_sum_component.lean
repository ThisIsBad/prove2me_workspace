import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 2, p. 13: for every graph `g` and component `S ∈ N/g`,
`∑_{i ∈ S} φ_i(v/g) = ∑_{R ∈ S/g} v_R`. -/
theorem shapley_restrict_sum_component {n : ℕ} (hn : 0 < n) (v : Game n) (g : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : S ∈ quot univ g) :
    ∑ i ∈ S, shapley (restrict v g) i = ∑ R ∈ quot S g, v R := by sorry

end CooperationGraphs.FairRule

