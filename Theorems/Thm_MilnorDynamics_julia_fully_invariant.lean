import Mathlib
import Definitions.Def_MilnorDynamics_RationalMaps

open scoped OnePoint Topology
open Filter Set

namespace MilnorDynamics

theorem julia_fully_invariant (f : RationalMap) (z : OnePoint ℂ) :
    z ∈ juliaSet f.toFun ↔ f.toFun z ∈ juliaSet f.toFun := by sorry

end MilnorDynamics
