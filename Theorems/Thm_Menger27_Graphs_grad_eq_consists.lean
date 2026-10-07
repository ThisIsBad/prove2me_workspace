import Mathlib
import Definitions.Def_Menger27_Graphs_Separation

namespace Menger27.Graphs

theorem grad_eq_consists {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (hG : NPointConnected G P Q n) (hgrad : G.edgeFinset.card = n) :
    ∃ (a b : Fin n → V) (w : ∀ i, G.Walk (a i) (b i)),
      (∀ i, a i ∈ P ∧ b i ∈ Q ∧ (w i).IsPath) ∧
      (∀ i j, i ≠ j → List.Disjoint (w i).support (w j).support) ∧
      ∀ e ∈ G.edgeSet, ∃ i, e ∈ (w i).edges := by sorry

end Menger27.Graphs

