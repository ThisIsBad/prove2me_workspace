import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic

namespace LogRegretOCO.ONS

/-- Lemma 11 (Hazan–Agarwal–Kale 2007, p. 190). Let `u_1, …, u_T ∈ ℝⁿ` with `‖u_t‖ ≤ r` for some
`r > 0`, let `ε > 0`, and let `V_t = Σ_{τ=1}^t u_τ u_τᵀ + ε Iₙ`. Then
`Σ_{t=1}^T u_tᵀ V_t⁻¹ u_t ≤ n log(r²T/ε + 1)`. -/
theorem elliptical_potential {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (T : ℕ) (hu : ∀ t ∈ Finset.Icc 1 T, ‖u t‖ ≤ r) :
    ∑ t ∈ Finset.Icc 1 T, quadForm (regGram ε u t)⁻¹ (u t) ≤
      n * Real.log (r ^ 2 * T / ε + 1) := by sorry

end LogRegretOCO.ONS

