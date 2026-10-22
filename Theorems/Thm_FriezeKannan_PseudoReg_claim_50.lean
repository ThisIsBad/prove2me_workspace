import Mathlib
import Definitions.Def_FriezeKannan_PseudoReg_Setting

namespace FriezeKannan.PseudoReg

theorem claim_50 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ)
    (s : ℕ) (Rs Cs : Fin s → Finset V) (d : Fin s → ℝ)
    (hD : ∀ S T : Finset V,
      |blockSum (G.adjMatrix ℝ - cutSum Rs Cs d) S T| ≤ ε * (Fintype.card V : ℝ) ^ 2) :
    IsPseudoRegular G (atomPartition Rs Cs) (2 * ε) := by sorry

end FriezeKannan.PseudoReg

