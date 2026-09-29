import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 286, Theorem 4.4, in the reading of Lemma 4.3 ("argmax(ω) is an integral base
set, that is, conv(argmax(ω)) is an integral base polytope"): on a finite integral base set `B`,
`ω` satisfies (EXC) iff `argmax(ω[p])` is an integral base set for every `p : V → ℝ`. -/
theorem exc_iff_argmax_isIntegralBaseSet {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ) :
    SatisfiesEXC B ω ↔ ∀ p : V → ℝ, IsIntegralBaseSet (argmaxB B (perturb ω p)) := by sorry

end SteinitzExchange.Extension
