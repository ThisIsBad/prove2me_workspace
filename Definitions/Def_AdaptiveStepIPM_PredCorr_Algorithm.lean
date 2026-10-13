import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

namespace AdaptiveStepIPM.PredCorr

/-- Every step up to θ remains in the outer neighborhood. -/
def PredictorAdmissible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (x s dx ds : Fin n → ℝ) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ ∀ u ∈ Set.Icc (0 : ℝ) θ,
    N2 A b c (1 / 2) (stepX x dx u) (stepS s ds u)

/-- One iteration of Algorithm 1, with the largest admissible predictor
step and one full corrector step. -/
def Alg1Step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s xNext sNext : Fin n → ℝ) : Prop :=
  ∃ (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (θbar : ℝ)
    (dx' : Fin n → ℝ) (dy' : Fin m → ℝ) (ds' : Fin n → ℝ),
    SearchDirection A x s 0 dx dy ds ∧
    IsGreatest {θ : ℝ | PredictorAdmissible A b c x s dx ds θ} θbar ∧
    SearchDirection A (stepX x dx θbar) (stepS s ds θbar) 1 dx' dy' ds' ∧
    xNext = stepX (stepX x dx θbar) dx' 1 ∧
    sNext = stepS (stepS s ds θbar) ds' 1

end AdaptiveStepIPM.PredCorr
