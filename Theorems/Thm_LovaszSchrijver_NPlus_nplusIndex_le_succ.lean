import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_StableSet

namespace LovaszSchrijver.NPlus

theorem nplusIndex_le_succ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (b : ℝ) (hvalid : Valid (STAB G) a b) (r : ℕ)
    (hcontract : ∀ v, 0 < a v → Valid (NplusG r G) (contractCoeff G a v) (b - a v)) :
    Valid (NplusG (r + 1) G) a b := by sorry

end LovaszSchrijver.NPlus

