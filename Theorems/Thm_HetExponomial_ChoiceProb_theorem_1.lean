import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace HetExponomial.ChoiceProb

theorem theorem_1 {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n) :
    choiceProb u lam i =
      G u lam i - ∑ k ∈ strictlyWorse u i, lam i / Lplus u lam k * G u lam k := by sorry

end HetExponomial.ChoiceProb

