import Mathlib
import Definitions.Def_TsengCGD_Global_Basic

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

theorem lemma2 {n : ℕ} (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (hs : Standing f D P c)
    (x : Vec n) (hx : x ∈ D) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef) :
    IsStationary f D P c x ↔ dH f D P c H x Finset.univ = 0 := by sorry

end TsengCGD.Global

