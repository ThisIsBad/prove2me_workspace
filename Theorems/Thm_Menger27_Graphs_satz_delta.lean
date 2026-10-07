import Mathlib
import Definitions.Def_Menger27_Graphs_Separation

namespace Menger27.Graphs

theorem satz_delta {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P Q : Finset V) (hPQ : Disjoint P Q) (n : ℕ) (hG : NPointConnected G P Q n) :
    HasDisjointPaths G P Q n := by sorry

end Menger27.Graphs

