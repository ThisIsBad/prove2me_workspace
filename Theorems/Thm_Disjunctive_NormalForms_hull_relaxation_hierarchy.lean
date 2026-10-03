import Mathlib
import Definitions.Def_Disjunctive_NormalForms_Basic

namespace Disjunctive.NormalForms

/-- Theorem 4.7 (Balas §4.2, p. 53-54): for a sequence of regular forms `F_0, …, F_t` of a
disjunctive set, with `F_0` in CNF, `F_t` in DNF, and each `F_i` obtained from `F_{i-1}` by a
basic step, the hull-relaxations form a chain `P₀ = h-relF₀ ⊇ h-relF₁ ⊇ ⋯ ⊇ h-relF_t = cl conv
F_t`. -/
theorem hull_relaxation_hierarchy {n t : ℕ} (T : Fin (t + 1) → Type*) [∀ i, Fintype (T i)]
    (S : (i : Fin (t + 1)) → T i → Set (Fin n → ℝ)) (hCNF : ∀ j, IsElementaryDisjunction (S 0 j))
    (hDNF : Fintype.card (T (Fin.last t)) = 1)
    (hSteps : ∀ i : Fin t, IsBasicStepOf (S i.castSucc) (S i.succ)) :
    P0Set (S 0) = HRel (S 0) ∧
      (∀ i : Fin t, HRel (S i.succ) ⊆ HRel (S i.castSucc)) ∧
      HRel (S (Fin.last t)) = closure (convexHull ℝ (⋂ j, S (Fin.last t) j)) := by sorry

end Disjunctive.NormalForms

