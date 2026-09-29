import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 282, Theorem 3.1: on a finite integral base set, (EXC) ⇔ (EXC_loc). -/
theorem exc_iff_exc_loc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ SatisfiesEXCLoc B ω := by sorry

end SteinitzExchange.Extension
