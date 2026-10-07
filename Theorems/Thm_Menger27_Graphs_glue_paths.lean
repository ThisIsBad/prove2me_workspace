import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts

namespace Menger27.Graphs

theorem glue_paths {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ)
    (S : Finset V) (hS : Separates G P Q S) (hcard : S.card = n)
    (hP : HasDisjointPaths (sidePart G P S) (P \ S) (S \ P) (n - (S ∩ P).card))
    (hQ : HasDisjointPaths (sidePart G Q S) (Q \ S) (S \ Q) (n - (S ∩ Q).card)) :
    HasDisjointPaths G P Q n := by sorry

end Menger27.Graphs

