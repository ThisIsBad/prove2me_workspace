import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem euler_tour_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) :
    (∀ v, Even (G.degree v)) ↔ ∃ (v : V) (p : G.Walk v v), p.IsEulerian := by sorry

end SupplyChainTheory
