import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem julia_set_iterate_eq (f : RationalMap) (hf : 1 ≤ f.degree) (k : ℕ) (hk : 0 < k) :
    juliaSet (f.toFun^[k]) = juliaSet f.toFun := by sorry

end MilnorDynamics
