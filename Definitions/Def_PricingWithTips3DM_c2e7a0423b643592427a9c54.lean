import Definitions.Def_PricingWithTips3DM_203c6716e98c62775fda1e5e
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# General-circuit formula emitter

Public facade for the fixed TM2 that emits the canonical SAT formula from a
guarded normalized circuit record, together with its polynomial runtime proof.
-/
