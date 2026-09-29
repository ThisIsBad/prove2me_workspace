import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_Constraints

namespace LovaszSchrijver.NPlus

theorem nplusIndex_eq_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ∀ v, ∃ w, G.Adj v w) :
    (∀ B : Finset V, G.IsClique (B : Set V) → 3 ≤ B.card →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi B) 1} 1) ∧
    (∀ C : Finset V, IsOddHole G C →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi C) (((C.card : ℝ) - 1) / 2)} 1) ∧
    (∀ U : Finset V, ∀ u₀ : V, IsOddWheel G U u₀ →
        IsLeast {t : ℕ | Valid (NplusG t G) (wheelCoeff U u₀) (((U.card : ℝ) - 2) / 2)} 1) ∧
    (∀ D : Finset V, IsOddAntihole G D →
        IsLeast {t : ℕ | Valid (NplusG t G) (chi D) 2} 1) := by sorry

end LovaszSchrijver.NPlus

