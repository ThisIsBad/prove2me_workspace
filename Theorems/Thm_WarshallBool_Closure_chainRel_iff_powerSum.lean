import Mathlib
import Definitions.Def_WarshallBool_Closure_Setting

namespace WarshallBool.Closure

/-- Warshall (1962), p. 11, footnote 2: the chain definition of `M′` in the THEOREM agrees
with the introduction's `M′ = ∨_{p=1}^{d} M^p`. -/
theorem chainRel_iff_powerSum {d : ℕ} (M : Fin d → Fin d → Bool) (i j : Fin d) :
    ChainRel M i j ↔ powerSum M i j = true := by sorry

end WarshallBool.Closure

