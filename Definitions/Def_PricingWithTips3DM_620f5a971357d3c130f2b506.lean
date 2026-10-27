import Definitions.Def_PricingWithTips3DM_17bc4cd8bcb52c788f9df635
import Definitions.Def_PricingWithTips3DM_3f22bafa32531f59b5d9c486
import Definitions.Def_PricingWithTips3DM_8312d519dd54bd0a5e3390ec
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Whole-tableau row layout

This facade exports consecutive row intervals, proof-carrying serial input-gate
allocation, and exact per-row assignment semantics.  It does not assemble
boundary or transition constraints.
-/
