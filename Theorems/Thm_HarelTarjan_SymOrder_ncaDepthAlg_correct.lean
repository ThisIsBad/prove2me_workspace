import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym
import Definitions.Def_HarelTarjan_SymOrder_Algorithms

namespace HarelTarjan.SymOrder

/-- The algorithm to solve the nca depth problem (§3, p. 342) is correct: for all vertices `v`,
`w`, it returns the depth of the nearest common ancestor of `v` and `w`. -/
theorem ncaDepthAlg_correct {d : ℕ} (v w : Vertex d) :
    ncaDepthAlg v w = depth (nca v w) := by sorry

end HarelTarjan.SymOrder
