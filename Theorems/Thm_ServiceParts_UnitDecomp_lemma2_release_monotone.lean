import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model
import Definitions.Def_ServiceParts_UnitDecomp_Subsystem

namespace ServiceParts.UnitDecomp

theorem lemma2_release_monotone {σ : Type} [Fintype σ] (M : Model σ) (N n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (s : σ) (y : ℕ) (hy : 1 ≤ y)
    (hrel : M.optDecisions N n s (y + 1) = {Decision.release}) :
    Decision.release ∈ M.optDecisions N n s y := by sorry

end ServiceParts.UnitDecomp

