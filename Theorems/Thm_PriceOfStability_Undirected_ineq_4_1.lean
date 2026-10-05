import Definitions.Def_PriceOfStability_Undirected_Model
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- Inequality (4.1) (Anshelevich et al., SIAM J. Comput. 38 (2008), Claim 4.1, proof, (4.1),
p. 1613, PDF p. 12). In the two-player undirected fair connection game with nonnegative edge costs,
from every profile `(S₁, S₂)` a Nash equilibrium `(S′₁, S′₂)` is reachable whose two-player potential
does not exceed that of `(S₁, S₂)`:
`y₁ + y₂ + (3/2)y₃ ≤ x₁ + x₂ + (3/2)x₃`, where `x₁ = cost(S₁∖S₂)`, `x₂ = cost(S₂∖S₁)`,
`x₃ = cost(S₁∩S₂)` and `y₁, y₂, y₃` are the same quantities for `(S′₁, S′₂)`.

**Formalization Note.** The paper's `S′` is "a Nash equilibrium that a series of improving responses
converges to starting with (S₁, S₂)"; the statement asserts the existence of a pure Nash equilibrium
satisfying (4.1), which is what the proof of Claim 4.1 uses. Players `0`, `1` are the paper's 1, 2. -/
theorem ineq_4_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e) (S : Fin 2 → Finset (Sym2 V))
    (hS : IsProfile (twoPlayerGame G c s t) S) :
    ∃ S' : Fin 2 → Finset (Sym2 V), IsPureNash (twoPlayerGame G c s t) S' ∧
      setCost c (S' 0 \ S' 1) + setCost c (S' 1 \ S' 0) + 3 / 2 * setCost c (S' 0 ∩ S' 1) ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + 3 / 2 * setCost c (S 0 ∩ S 1) := by sorry

end PriceOfStability.Undirected

