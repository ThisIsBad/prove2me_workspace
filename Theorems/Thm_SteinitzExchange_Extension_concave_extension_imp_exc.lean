import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 288, Theorem 4.6 (Extension Theorem), reverse direction. Let `B ⊆ ℤ^V` be a finite
integral base set and `ω : B → ℝ` a function. Suppose `ω` extends to a concave function
`ω̄ : B̄ → ℝ` agreeing with `ω` on `B` whose maximizers over `B̄` of `ω̄[p](b) = ω̄(b) + ⟨p, b⟩`
are integral base polytopes for every `p : V → ℝ`. Then `ω` satisfies the exchange property (EXC).

This is the converse half of the Extension Theorem: the combinatorial condition on the maximizer
sets of all linear perturbations forces the base-exchange inequality
$$\omega(x) + \omega(y) \le \omega(x - \chi_u + \chi_v) + \omega(y + \chi_u - \chi_v)$$
whenever `x, y ∈ B` and `u ∈ supp⁺(x − y)`. The argument proceeds by contradiction: if the
exchange inequality fails for some `x, y, u`, one produces a linear functional `p` (a supporting
separator at a maximizing face) whose maximizer set over `B̄` cannot be an integral base polytope,
contradicting the hypothesis. -/
theorem concave_extension_imp_exc {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : IsIntegralBaseSet B) (ω : (V → ℤ) → ℝ)
    (ωbar : (V → ℝ) → ℝ)
    (hconc : ConcaveOn ℝ (hull B) ωbar)
    (hext : ∀ x ∈ B, ωbar (toReal x) = ω x)
    (hpoly : ∀ p : V → ℝ, IsIntegralBasePolytope (argmaxOn (hull B) (fun b => ωbar b + pairing p b))) :
    SatisfiesEXC B ω := by sorry

end SteinitzExchange.Extension
