import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting

namespace ChenStein.OneVar

open scoped NNReal

/-- Arratia--Goldstein--Gordon (1989), §4, p. 21, last clause of Lemma 1. -/
theorem lemma_1_furthermore (lam : ℝ≥0) (hlam : 0 < lam) :
    (∀ w, |S lam (fun k => (if k = 0 then 1 else 0) - Real.exp (-(lam : ℝ))) w| ≤
      (1 - Real.exp (-(lam : ℝ))) / (lam : ℝ)) ∧
    (∃ w, |S lam (fun k => (if k = 0 then 1 else 0) - Real.exp (-(lam : ℝ))) w| =
      (1 - Real.exp (-(lam : ℝ))) / (lam : ℝ)) := by sorry

end ChenStein.OneVar

