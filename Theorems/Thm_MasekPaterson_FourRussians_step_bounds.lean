import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

/-- Lemma 3: if every insertion cost is at most `I` and every deletion cost at most `D`
(in particular for `I = max_a I_a`, `D = max_a D_a` over a finite alphabet), then for all
strings `A, B` and `1 ≤ i ≤ |A|`, `1 ≤ j ≤ |B|`:
(i) `−I ≤ δ_{i,j} − δ_{i−1,j} ≤ D`, and (ii) `−D ≤ δ_{i,j} − δ_{i,j−1} ≤ I`. -/
theorem step_bounds {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (I D : ℝ) (hI : ∀ a : α, insCost γ a ≤ I) (hD : ∀ a : α, delCost γ a ≤ D)
    (A B : List α) (i j : ℕ)
    (hi : 1 ≤ i) (hiA : i ≤ A.length) (hj : 1 ≤ j) (hjB : j ≤ B.length) :
    (-I ≤ dmat γ A B i j - dmat γ A B (i - 1) j ∧ dmat γ A B i j - dmat γ A B (i - 1) j ≤ D) ∧
    (-D ≤ dmat γ A B i j - dmat γ A B i (j - 1) ∧ dmat γ A B i j - dmat γ A B i (j - 1) ≤ I) := by sorry

end MasekPaterson.FourRussians

