import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 288, Lemma 4.5: if `ω` satisfies (EXC) on the finite integral base set `B`,
then its concave closure agrees with it on `B`: `ω̂(x) = ω(x)` for all `x ∈ B`. -/
theorem concaveClosure_eq_of_exc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (hω : SatisfiesEXC B ω) :
    ∀ x ∈ B, concaveClosure B ω (toReal x) = ω x := by sorry

end SteinitzExchange.Extension
