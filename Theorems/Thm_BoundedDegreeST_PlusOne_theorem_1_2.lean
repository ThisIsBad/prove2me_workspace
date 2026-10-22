import Definitions.Def_BoundedDegreeST_PlusOne_Algorithm

namespace BoundedDegreeST.PlusOne

/-- Singh–Lau, Theorem 1.2, p. 661, via Figure 4 at `F = ∅`, `W = V`. -/
theorem theorem_1_2 {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (c : Sym2 V → ℝ) (B : V → ℤ)
    (hsimple : SimpleEdges E)
    (hfeasible : ∃ x, Feasible E B Finset.univ ∅ x) :
    (∃ T, Returns c (initial E B) T) ∧
    (∀ k, Chain c (initial E B) k →
      (k : ℤ) ≤ 2 * (Fintype.card V : ℤ) - 1) ∧
    (∀ T, Returns c (initial E B) T →
      T ⊆ E ∧ IsSpanningTree T ∧
      (∀ v : V, (degree T v : ℤ) ≤ B v + 1) ∧
      (∀ x, Feasible E B Finset.univ ∅ x →
        cost c T ≤ ∑ e ∈ E, c e * x e) ∧
      (∀ T₀ : Finset (Sym2 V), T₀ ⊆ E → IsSpanningTree T₀ →
        (∀ v : V, (degree T₀ v : ℤ) ≤ B v) →
        cost c T ≤ cost c T₀)) := by sorry
end BoundedDegreeST.PlusOne

