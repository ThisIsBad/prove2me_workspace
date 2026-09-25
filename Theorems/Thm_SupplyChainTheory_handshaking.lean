import Definitions.Def_SupplyChainTheory_tsp

open Classical

namespace SupplyChainTheory

theorem handshaking {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (Finset.univ.filter (fun v => Odd (G.degree v))).card := by sorry

end SupplyChainTheory
