import Mathlib
import Definitions.Def_BertsekasSPGraph
import Definitions.Def_SendSplit_DPEquations_Bellman

namespace SendSplit.DPEquations

theorem bellman_unique_solution {V : Type} [Fintype V] [DecidableEq V]
    (G : BertsekasSPGraph V)
    (hloop : ∀ i, (i, i) ∉ G.arcs) (hout : ∀ j, (G.t, j) ∉ G.arcs)
    (hpos : ∀ l, IsSimpleCircuit G l → 0 < circuitLength G l) :
    ∀ C : V → EReal, IsBellmanSolution G C → ∀ k, C k = BertsekasShortestDistance G k G.t := by sorry

end SendSplit.DPEquations

