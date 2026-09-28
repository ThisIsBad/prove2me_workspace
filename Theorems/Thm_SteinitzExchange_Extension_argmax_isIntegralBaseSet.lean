import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 285, Lemma 4.3: if `ω` satisfies (EXC) on the finite integral base set `B`,
then `argmax(ω)` is an integral base set. -/
theorem argmax_isIntegralBaseSet {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    IsIntegralBaseSet (argmaxB B ω) := by sorry

end SteinitzExchange.Extension
