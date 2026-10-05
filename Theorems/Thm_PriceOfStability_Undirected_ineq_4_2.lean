import Definitions.Def_PriceOfStability_Undirected_Model
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- Inequality (4.2) (Anshelevich et al., SIAM J. Comput. 38 (2008), Claim 4.1, proof, (4.2),
p. 1613, PDF p. 12). Under the hypotheses of the deviation inequalities — `(S′₁, S′₂)` a Nash
equilibrium of the two-player undirected fair connection game with nonnegative edge costs, `(S₁, S₂)`
a profile of inclusion-minimal strategies — `y₁/2 + y₂/2 ≤ 2x₁ + 2x₂`, where
`x₁ = cost(S₁∖S₂)`, `x₂ = cost(S₂∖S₁)`, `y₁ = cost(S′₁∖S′₂)`, `y₂ = cost(S′₂∖S′₁)`.

**Formalization Note.** The inclusion-minimality of `S₁`, `S₂` is implicit in the paper (see
`deviation_inequality`). Players `0`, `1` are the paper's 1, 2. -/
theorem ineq_4_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e)
    (S S' : Fin 2 → Finset (Sym2 V)) (hS : ∀ i, IsMinimalStrategy G s t i (S i))
    (hS' : IsPureNash (twoPlayerGame G c s t) S') :
    setCost c (S' 0 \ S' 1) / 2 + setCost c (S' 1 \ S' 0) / 2 ≤
      2 * setCost c (S 0 \ S 1) + 2 * setCost c (S 1 \ S 0) := by sorry

end PriceOfStability.Undirected

