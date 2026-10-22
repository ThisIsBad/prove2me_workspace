import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem lemma3 {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (H Ht : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) (hHt : Ht.PosDef) :
    let d := dH f D P c H x J
    let dt := dH f D P c Ht x J
    ‖dt‖ ≤
      ((1 + genMax H Ht J +
        Real.sqrt (1 - 2 * genMin H Ht J + (genMax H Ht J) ^ 2)) / 2) *
        (lamMax H J / lamMin Ht J) * ‖d‖ ∧
    ((∀ u : Vec n, SupportedOn J u → u ≠ 0 → qf Ht u < qf H u) →
      ‖d‖ ≤ Real.sqrt (lamMax (H - Ht) J / lamMin (H - Ht) J) * ‖dt‖) := by sorry

end TsengCGD.Global

