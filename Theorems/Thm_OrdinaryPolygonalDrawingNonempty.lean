import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

lemma OrdinaryPolygonalDrawingNonempty {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    Nonempty (OrdinaryPolygonalDrawing G) := by sorry
