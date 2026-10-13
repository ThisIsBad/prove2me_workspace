import Mathlib
import Definitions.Def_BertsekasSPGraph
import Definitions.Def_SendSplit_DPEquations_Bellman

namespace SendSplit.DPEquations

theorem bellman_greatest_solution {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V)
    (hloop : ∀ i, (i, i) ∉ G.arcs) (hout : ∀ j, (G.t, j) ∉ G.arcs)
    (hcirc : ∀ l, IsSimpleCircuit G l → 0 ≤ circuitLength G l) :
    IsBellmanSolution G (fun k => BertsekasShortestDistance G k G.t) ∧
      (∀ k, BertsekasShortestDistance G k G.t = ⊤ ∨
        ∃ l, BertsekasIsWalkFrom G k G.t l ∧
          ((BertsekasWalkLength G l : ℝ) : EReal) = BertsekasShortestDistance G k G.t) ∧
      (∀ C : V → EReal, IsBellmanSolution G C → ∀ k, C k ≤ BertsekasShortestDistance G k G.t) ∧
      (∀ G' : BertsekasSPGraph V, G'.t = G.t → G'.arcs ⊆ G.arcs →
        (∀ p ∈ G'.arcs, G.length p.1 p.2 ≤ G'.length p.1 p.2) →
        ∀ k, BertsekasShortestDistance G k G.t ≤ BertsekasShortestDistance G' k G'.t) := by sorry

end SendSplit.DPEquations

