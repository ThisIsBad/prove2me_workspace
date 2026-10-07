import Mathlib
import Definitions.Def_PolicyGradTheory_QNPG_Setting

namespace PolicyGradTheory.QNPG

/-- Remark 6.7, p. 33, with smoothness understood as the gradient-Lipschitz
condition preceding (24), p. 37. -/
theorem log_linear_smooth {S A : Type} [Fintype A] [Nonempty A] {d : ℕ}
    (φ : S → A → EuclideanSpace ℝ (Fin d)) (B : ℝ)
    (hφ : ∀ s a, ‖φ s a‖ ≤ B) (s : S) (a : A) :
    ∀ θ θ' : EuclideanSpace ℝ (Fin d),
      ‖gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ -
        gradient (fun x => Real.log (logLinearPolicy φ x s a)) θ'‖ ≤
        B ^ 2 * ‖θ - θ'‖ := by sorry

end PolicyGradTheory.QNPG

