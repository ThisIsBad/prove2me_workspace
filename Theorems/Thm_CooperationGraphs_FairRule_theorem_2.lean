import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Theorem 2 (p. 8): the fair allocation rule `Y` for `v` satisfies `Y(g) = φ(v/g)` for every
graph `g`; in particular `Y(ḡ^N) = φ(v)`. -/
theorem theorem_2 {n : ℕ} (hn : 0 < n) (v : Game n) (Y : Rule n) (hY : IsFair v Y) :
    (∀ g : SimpleGraph (Fin n), Y g = shapley (restrict v g)) ∧ Y ⊤ = shapley v := by sorry

end CooperationGraphs.FairRule

