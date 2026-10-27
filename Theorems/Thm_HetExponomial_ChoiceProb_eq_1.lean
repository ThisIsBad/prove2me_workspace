import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace HetExponomial.ChoiceProb

theorem eq_1 {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n) :
    choiceProb u lam i =
        ∫ z in Set.Ioi 0,
          (∏ j ∈ Finset.univ.erase i, (1 - cdfExp (lam j) (u j - u i + z))) * pdfExp (lam i) z ∧
      choiceProb u lam i =
        ∫ z in Set.Ioi 0, lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) := by sorry

end HetExponomial.ChoiceProb

