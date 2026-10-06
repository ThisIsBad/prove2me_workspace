import Mathlib
import Definitions.Def_ServiceParts_UnitDecomp_Model
import Definitions.Def_ServiceParts_UnitDecomp_Subsystem

namespace ServiceParts.UnitDecomp

theorem critical_distance_policy_optimal {σ : Type} [Fintype σ] (M : Model σ) (N n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) (s : σ) (z y : ℕ) (hzy : z = M.m + 1 → 1 ≤ y) :
    M.subCost N (M.criticalPolicy N) n s (z, y) = M.subOpt N n s (z, y) := by sorry

end ServiceParts.UnitDecomp

