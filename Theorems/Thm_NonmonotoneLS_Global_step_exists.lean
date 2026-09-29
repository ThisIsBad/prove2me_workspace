import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

namespace NonmonotoneLS.Global

/-- Lemma 1.1, second sentence (p. 1045): if `∇f(x) d < 0`, `f` is bounded from below and the
reference value satisfies `f(x) ≤ C`, then a nonmonotone Wolfe step exists, and for every trial
step `ᾱ > 0` there is a largest integer `h` with `ᾱ ρ^h` satisfying (1.4) and `ᾱ ρ^h ≤ μ`. -/
theorem step_exists {n : ℕ} (p : Shared.Params) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : EuclideanSpace ℝ (Fin n)) (C : ℝ) (hC : f x ≤ C)
    (hdesc : ⟪gradient f x, d⟫_ℝ < 0) :
    (∃ α : ℝ, Shared.IsWolfeStep p f x d C α) ∧
      ∀ αbar : ℝ, 0 < αbar → ∃ h : ℤ, IsGreatest (Shared.armijoAdmissible p f x d C αbar) h := by sorry

end NonmonotoneLS.Global

