import Mathlib
import Definitions.Def_RetailVariety_Statics_Model

open Filter Topology

namespace RetailVariety.Statics

theorem lhs13_increasing_in_p (c lam σ β : ℝ) (hc : 0 < c) (hlam : 0 < lam) (hσ : 0 < σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    StrictMonoOn (fun p : ℝ => criticalFractile p c) (Set.Ioi c) ∧
      StrictMonoOn (fun p : ℝ => (1 - c / p) * (Real.sqrt (2 * Real.pi) / σ) * lam ^ (1 - β)
          * Real.exp (criticalFractile p c ^ 2 / 2)) (Set.Ioi c) := by sorry

end RetailVariety.Statics

