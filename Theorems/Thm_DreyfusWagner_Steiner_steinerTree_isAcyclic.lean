import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem

namespace DreyfusWagner.Steiner

/-- Dreyfus–Wagner 1971, §1, p. 197: a Steiner path `S` must be a tree, i.e. it contains no
cycles. -/
theorem steinerTree_isAcyclic {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (Y : Finset V) (S : Finset (Sym2 V)) (hS : IsSteinerTree G ℓ Y S) :
    (SimpleGraph.fromEdgeSet (S : Set (Sym2 V))).IsAcyclic := by sorry

end DreyfusWagner.Steiner
