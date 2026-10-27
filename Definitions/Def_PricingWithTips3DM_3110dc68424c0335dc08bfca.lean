import Definitions.Def_PricingWithTips3DM_8c1f84a611ea452f3486eb9b
import Definitions.Def_PricingWithTips3DM_d2a81b4fbc82d2cc5bdc499c
import Definitions.Def_PricingWithTips3DM_1605d2d02ad208ee48a25997
import Definitions.Def_PricingWithTips3DM_a2c7760aae7a9696307d4848
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# CLRS Section 34.4 - Exact tableau boundary constraints

This facade exports zero-gate pool-backed static rows, total concrete initial
and accepting constraints, and the symbolic-input initial form needed by the
whole-tableau verifier.  Both concrete constructors reject unencodable targets
with an actual constant-false circuit output.
-/
