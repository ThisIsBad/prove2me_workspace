import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem prox_indicator_eq_projection {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hC_ne : C.Nonempty)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∃! x, IsProjection C v x) ∧
      ∀ ρ : ℝ, 0 < ρ → ∀ x, IsProx C (fun _ => 0) ρ v x ↔ IsProjection C v x := by sorry

end BoydADMM.Prox

