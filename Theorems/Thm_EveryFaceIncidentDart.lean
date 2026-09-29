import Definitions.Def_PlaneFaceData
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Classical
noncomputable section

lemma EveryFaceIncidentDart {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] [DecidableRel G.Adj] (D : OrdinaryPolygonalDrawing G)
    (hD : D.crossingSet.card = 0) (A : PlaneFaceData G D) :
    G.Connected → 3 ≤ Fintype.card V → 0 < G.edgeFinset.card →
      ∀ F : A.Face, ∃ d : G.Dart, A.leftFace d = F := by sorry
