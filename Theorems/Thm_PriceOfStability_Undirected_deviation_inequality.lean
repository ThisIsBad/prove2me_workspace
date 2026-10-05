import Definitions.Def_PriceOfStability_Undirected_Model
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- The deviation inequalities (Anshelevich et al., SIAM J. Comput. 38 (2008), Claim 4.1, proof,
p. 1613, PDF p. 12). Let `(S′₁, S′₂)` be a Nash equilibrium of the two-player undirected fair
connection game with nonnegative edge costs and `(S₁, S₂)` a profile in which each `Sᵢ` is an
inclusion-minimal strategy. With `xᵢ`, `yᵢ` as in (4.1), player 1's deviation to
`X₁ ∪ X₂ ∪ Y₂ ∪ Y₃` and player 2's symmetric deviation give
`x₁ + x₂ + y₂/2 + y₃/2 ≥ y₁ + y₃/2` and `x₁ + x₂ + y₁/2 + y₃/2 ≥ y₂ + y₃/2`.

**Formalization Note.** The inclusion-minimality of `S₁`, `S₂` is implicit in the paper, whose
argument ("following X₁ until X₁ meets with X₂, then following X₂ back to t₂") treats them as paths;
for arbitrary connecting sets `X₁ ∪ X₂` need not connect `t₁` with `t₂`. Players `0`, `1` are the
paper's 1, 2. -/
theorem deviation_inequality {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : Sym2 V → ℝ) (s : V) (t : Fin 2 → V) (hc : ∀ e, 0 ≤ c e)
    (S S' : Fin 2 → Finset (Sym2 V)) (hS : ∀ i, IsMinimalStrategy G s t i (S i))
    (hS' : IsPureNash (twoPlayerGame G c s t) S') :
    setCost c (S' 0 \ S' 1) + setCost c (S' 0 ∩ S' 1) / 2 ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + setCost c (S' 1 \ S' 0) / 2 +
          setCost c (S' 0 ∩ S' 1) / 2 ∧
      setCost c (S' 1 \ S' 0) + setCost c (S' 0 ∩ S' 1) / 2 ≤
        setCost c (S 0 \ S 1) + setCost c (S 1 \ S 0) + setCost c (S' 0 \ S' 1) / 2 +
          setCost c (S' 0 ∩ S' 1) / 2 := by sorry

end PriceOfStability.Undirected

