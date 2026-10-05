import Definitions.Def_PriceOfStability_Undirected_Model
open CongestionPoA.AsymSum

namespace PriceOfStability.Undirected

/-- Edge costs of the 3-node example of Sect. 4 (Anshelevich et al., SIAM J. Comput. 38 (2008),
p. 1613, PDF p. 12), on the vertices `0 = s`, `1 = t₁`, `2 = t₂`: the edges `(s, t₁)` and `(s, t₂)`
cost `2`, the edge `(t₁, t₂)` costs `1 + ε`.

**Formalization Note.** The diagonal pairs `s(v, v)` get cost `0`; they are not edges of a simple
graph and never belong to a strategy. -/
noncomputable def threeNodeCost (ε : ℝ) (e : Sym2 (Fin 3)) : ℝ :=
  if e = s(0, 1) ∨ e = s(0, 2) then 2 else if e = s(1, 2) then 1 + ε else 0

/-- The 3-node example of Sect. 4 (p. 1613, PDF p. 12): the complete graph on `{s, t₁, t₂}`
(`0, 1, 2`), common terminal `s = 0`, player `0` (the paper's player 1) connects `t₁ = 1` with `s`,
player `1` (the paper's player 2) connects `t₂ = 2` with `s`, edge costs `threeNodeCost ε`. -/
noncomputable def threeNode (ε : ℝ) : CongestionGame (Fin 2) (Sym2 (Fin 3)) :=
  twoPlayerGame ⊤ (threeNodeCost ε) 0 ![1, 2]

end PriceOfStability.Undirected
