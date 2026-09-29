import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem

namespace DreyfusWagner.Steiner

/-- Dreyfus–Wagner 1971, Appendix A, p. 205: the Steiner path connecting two nodes is the
shortest path between them, so its length is `D(i,j)`. -/
theorem steinerLength_pair_eq_pathDist {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected) (i j : V) :
    steinerLength G ℓ {i, j} = pathDist G ℓ i j := by sorry

end DreyfusWagner.Steiner
