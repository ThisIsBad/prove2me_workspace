import Mathlib
import Definitions.Def_SingleMachinePrec_Biclique_SG

namespace SingleMachinePrec.Biclique

/-- §9, p. 666 (proof of Lemma 9.1, upper bound). Let `G = (U, V, E)` be an `n`-by-`n` bipartite
graph and `(A, B)` an edge biclique of `G`. A sequence of all the jobs of `S_G` in the order
`U \ A → B → A → V \ B` exists; every such sequence observes the precedence constraints
`P = (U × V) \ E` of `S_G`, and its value is `n² − |A| · |B|`. -/
theorem upper_bound_schedule {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U]
    [DecidableEq V] (E : U → V → Prop) (n : ℕ) (hU : Fintype.card U = n)
    (hV : Fintype.card V = n) (A : Finset U) (B : Finset V) (hAB : IsEdgeBiclique E A B) :
    (∃ l : List (U ⊕ V), InBlockOrder A B l) ∧
      ∀ l : List (U ⊕ V), InBlockOrder A B l →
        LawlerPrec.MinMax.IsFeasible (precSG E) Finset.univ l ∧
          valSG l = (n : ℝ) ^ 2 - (A.card : ℝ) * (B.card : ℝ) := by sorry

end SingleMachinePrec.Biclique

