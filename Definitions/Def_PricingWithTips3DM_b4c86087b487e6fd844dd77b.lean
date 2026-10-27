import Definitions.Def_PricingWithTips3DM_c5fd22a06718898ef0cc9e70
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General CIRCUIT-SAT to SAT machine

Facade exporting the concrete fixed TM2, its guarded intermediate semantics,
and polynomial-time computation of `generalCircuitToSATMap`.
-/
