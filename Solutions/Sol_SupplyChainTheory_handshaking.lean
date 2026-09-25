import Mathlib
import Definitions.Def_SupplyChainTheory_tsp

open Classical

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Even (Finset.univ.filter (fun v => Odd (G.degree v))).card := by
  classical
  convert G.even_card_odd_degree_vertices
