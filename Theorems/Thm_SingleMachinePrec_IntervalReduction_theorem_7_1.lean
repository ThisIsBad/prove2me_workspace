import Mathlib
import Definitions.Def_AppliedComb_Posets_intervalOrder
import Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance

namespace SingleMachinePrec.IntervalReduction

/-- Theorem 7.1 (p. 661), in the form its proof (pp. 661–664) establishes: for a connected graph
`G` of maximum degree at most 3 with a rooted spanning tree numbered parent-first, the instance
`S` of Stage 2 (with `k = n² + 1`) has interval-order precedence constraints, and `G` has a vertex
cover of size at most `m` if and only if `⌊w(C_I)⌋ ≤ m + c`, where `c = |V| + |E \ E_T|`. -/
theorem theorem_7_1 {N : ℕ} (G : SimpleGraph (Fin N)) (hconn : G.Connected)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 3) (L : TreeLayout G) (m : ℕ) :
    AppliedComb.Posets.IsIntervalOrder (Job L) ∧
    ((∃ C : Finset (Fin N), G.IsVertexCover (C : Set (Fin N)) ∧ C.card ≤ m) ↔
      ⌊tauW L⌋₊ ≤ m + N + Fintype.card (NonTreeEdge L)) := by sorry

end SingleMachinePrec.IntervalReduction

