import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

namespace GavrilSubtree.Chordal

universe u

theorem maximal_insert_neighborSet {V : Type u} (G : SimpleGraph V) (v : V)
    (hv : IsSimplicial G v) : Maximal G.IsClique (insert v (G.neighborSet v)) := by sorry

end GavrilSubtree.Chordal

