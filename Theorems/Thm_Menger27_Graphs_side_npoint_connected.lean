import Mathlib
import Definitions.Def_Menger27_Graphs_Separation
import Definitions.Def_Menger27_Graphs_Parts

namespace Menger27.Graphs

theorem side_npoint_connected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n)
    (S : Finset V) (hS : Separates G P Q S) (hcard : S.card = n) :
    NPointConnected (sidePart G P S) (P \ S) (S \ P) (n - (S ∩ P).card) := by sorry

end Menger27.Graphs

