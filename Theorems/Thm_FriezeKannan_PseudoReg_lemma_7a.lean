import Mathlib
import Definitions.Def_FriezeKannan_PseudoReg_Setting

namespace FriezeKannan.PseudoReg

theorem lemma_7a {V : Type*} [Fintype V] [DecidableEq V]
    (A M : Matrix V V ℝ) (P Q : Finpartition (Finset.univ : Finset V)) (hQP : Q ≤ P)
    (hM : Compatible P M) (c : ℝ)
    (hc : ∀ S T : Finset V, |blockSum (A - M) S T| ≤ c) :
    ∀ S T : Finset V, |blockSum (A - blockAvg Q A) S T| ≤ 2 * c := by sorry

end FriezeKannan.PseudoReg

