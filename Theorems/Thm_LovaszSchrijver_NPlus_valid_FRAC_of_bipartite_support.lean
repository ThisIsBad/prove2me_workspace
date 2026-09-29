import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_StableSet

namespace LovaszSchrijver.NPlus

theorem valid_FRAC_of_bipartite_support {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) (a : V → ℝ) (b : ℝ)
    (hvalid : Valid (STAB G) a b) (hbip : (G.induce {i | a i ≠ 0}).Colorable 2) :
    Valid (FRAC G) a b := by sorry

end LovaszSchrijver.NPlus

