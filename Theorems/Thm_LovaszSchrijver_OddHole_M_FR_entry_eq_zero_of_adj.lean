import Mathlib
import Definitions.Def_LovaszSchrijver_OddHole_MatrixCone
import Definitions.Def_LovaszSchrijver_OddHole_StableSetCones

namespace LovaszSchrijver.OddHole

/-- Section 2.b, p. 177: if `Y = (yᵢⱼ) ∈ M(FR(G))` then `yᵢⱼ = 0` whenever `ij ∈ E(G)`. -/
theorem M_FR_entry_eq_zero_of_adj {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (Y : Matrix (Option V) (Option V) ℝ) (hY : Y ∈ M (FR G) (Q V))
    (i j : V) (hij : G.Adj i j) :
    Y (some i) (some j) = 0 := by sorry

end LovaszSchrijver.OddHole
