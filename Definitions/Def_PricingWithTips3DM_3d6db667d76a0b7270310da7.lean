import Definitions.Def_PricingWithTips3DM_721f794548f7ab30ee87b429
import Definitions.Def_PricingWithTips3DM_988b27bbcd4d2ab75ab2bc8b
import Definitions.Def_PricingWithTips3DM_4b980954d6b62a2c27f2ef21
import Definitions.Def_PricingWithTips3DM_5fc58927ed5a605607eb44af
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Internal encoding for the concrete general-circuit-to-SAT machine

This facade exports the guarded finite alphabet, its complete parser, exact
round-trip theorems, and the quadratic size bounds used by the later TM2
controllers.
-/
