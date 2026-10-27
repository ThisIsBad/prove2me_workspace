import Mathlib
import Definitions.Def_HetExponomial_ChoiceProb_Model

namespace HetExponomial.ChoiceProb

theorem eq_16 {n : ℕ} (hn : 2 ≤ n) (u lam : Fin n → ℝ) (hlam : ∀ j, 0 < lam j) (i : Fin n)
    (k : Fin (levels u).card) (hk : level u k = u i) :
    ∫ z in Set.Ioi 0, lam i * Real.exp (-(∑ j, lam j * max (u j - u i + z) 0)) =
      lam i * ∑ w ∈ Finset.univ.filter (fun w => w ≤ k),
        (tailInt u lam i (level u w) (u i - level u w) -
          if 0 < w.val then
            tailInt u lam i (level u w)
              (u i - level u ⟨w.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) w.isLt⟩)
          else 0) := by sorry

end HetExponomial.ChoiceProb

