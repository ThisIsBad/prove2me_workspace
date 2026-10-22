import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Theorem 4.2, p. 666, with the recursion and LP bound explicit. -/
theorem theorem_4_2 {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (I : Instance V)
    (hvalid : Valid I) (hfeasible : ∃ x, Feasible I.E I.B I.W I.F x) :
    (∃ H, Returns c I H) ∧
    (∀ k, Chain c I k →
      (k : ℤ) ≤ (Fintype.card V : ℤ) - (I.F.card : ℤ) - 1 + (I.W.card : ℤ)) ∧
    (∀ H, Returns c I H →
      H ⊆ I.E ∧ IsSpanningTree (H ∪ I.F) ∧
      (∀ v ∈ I.W, (degree H v : ℤ) ≤ I.B v + 1) ∧
      (∀ x, Feasible I.E I.B I.W I.F x →
        cost c H ≤ ∑ e ∈ I.E, c e * x e)) := by sorry
end BoundedDegreeST.PlusOne

