import Mathlib
import Definitions.Def_LogRegretOCO_EWOO_IsExpConcave
import Definitions.Def_LogRegretOCO_EWOO_shrunkSet

namespace LogRegretOCO.EWOO

/-- §3.4, displays on p. 187 (Hazan–Agarwal–Kale 2007): on the shrunken set
`S = {T/(T+1) x* + 1/(T+1) y : y ∈ P}`, each `h_t = exp(-α f_t)` satisfies
`h_t(x) ≥ T/(T+1) h_t(x*)`, hence
`∏_{τ=1}^T h_τ(x) ≥ (T/(T+1))^T ∏_{τ=1}^T h_τ(x*) ≥ (1/e) ∏_{τ=1}^T h_τ(x*)`. -/
theorem shrunk_set_bound (n : ℕ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (hPconv : Convex ℝ P) (α : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hexp : ∀ t, IsExpConcave α P (f t))
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ P) (T : ℕ) :
    (∀ t, ∀ x ∈ shrunkSet P xstar T,
        ((T : ℝ) / ((T : ℝ) + 1)) * Real.exp (-α * f t xstar) ≤ Real.exp (-α * f t x)) ∧
    (∀ x ∈ shrunkSet P xstar T,
        ((T : ℝ) / ((T : ℝ) + 1)) ^ T * ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
            ≤ ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ x) ∧
          (1 / Real.exp 1) * ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)
            ≤ ((T : ℝ) / ((T : ℝ) + 1)) ^ T *
                ∏ τ ∈ Finset.Icc 1 T, Real.exp (-α * f τ xstar)) := by sorry

end LogRegretOCO.EWOO

