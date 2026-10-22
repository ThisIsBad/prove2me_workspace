import Mathlib
import Definitions.Def_FriezeKannan_PseudoReg_Setting

namespace FriezeKannan.PseudoReg

theorem eq_47 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : Finpartition (Finset.univ : Finset V)) (S T : Finset V) (hST : Disjoint S T) :
    blockSum (G.adjMatrix ℝ) S T = ((G.interedges S T).card : ℝ) ∧
    blockSum (blockAvg Q (G.adjMatrix ℝ)) S T =
      ∑ Vi ∈ Q.parts, ∑ Vj ∈ Q.parts,
        (G.edgeDensity Vi Vj : ℝ) * ((S ∩ Vi).card : ℝ) * ((T ∩ Vj).card : ℝ) ∧
    blockSum (G.adjMatrix ℝ) S T - blockSum (blockAvg Q (G.adjMatrix ℝ)) S T =
      delta G Q S T := by sorry

end FriezeKannan.PseudoReg

