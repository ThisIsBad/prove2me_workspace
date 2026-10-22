import Definitions.Def_BoundedDegreeST_LowerUpper_Algorithm

namespace BoundedDegreeST.LowerUpper

/-- Singh–Lau, Theorem 5.2, p. 668: MBDCT Algorithm2 is a
`(1, A_v − 1, B_v + 1)`-approximation for the minimum bounded degree connecting
tree problem. On a well-formed instance whose LP is feasible:
(1) some run returns; (2) every run makes at most `|V| − |F| − 1 + |U ∪ W|`
iterations (the LP is solved by an oracle); (3) every returned `H` is an
`F`-tree in `E` with `c(H)` at most the BoundedDegreeST.PlusOne.cost of every feasible LP solution
and `A_v − 1 ≤ d_H(v)` on `U`, `d_H(v) ≤ B_v + 1` on `W`. -/
theorem theorem_5_2 {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (I : Instance V)
    (hvalid : Valid I) (hfeasible : ∃ x, Feasible I.E I.A I.B I.U I.W I.F x) :
    (∃ H, Returns c I H) ∧
    (∀ k, Chain c I k →
      (k : ℤ) ≤ (Fintype.card V : ℤ) - (I.F.card : ℤ) - 1 + ((I.U ∪ I.W).card : ℤ)) ∧
    (∀ H, Returns c I H →
      H ⊆ I.E ∧ BoundedDegreeST.PlusOne.IsSpanningTree (H ∪ I.F) ∧
      (∀ x, Feasible I.E I.A I.B I.U I.W I.F x →
        BoundedDegreeST.PlusOne.cost c H ≤ ∑ e ∈ I.E, c e * x e) ∧
      (∀ v ∈ I.U, I.A v - 1 ≤ (degree H v : ℤ)) ∧
      (∀ v ∈ I.W, (degree H v : ℤ) ≤ I.B v + 1)) := by sorry

end BoundedDegreeST.LowerUpper

