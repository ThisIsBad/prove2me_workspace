import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret (1997), §2.2, Lemma 2.2, "only if" direction, p. 1038 (PDF p. 4),
**corrected**: stated under `T₂ ≠ 0 ∨ T₃ = 0`. As printed (without that hypothesis) the
direction is false: `d = k = l = 1`, `T₁ = T₂ = T₄ = 0`, `T₃ = 1` gives `T(Δ) ≡ 0 ⪰ 0` and
`det(I − T₄Δ) = 1`, but `[[0, 1], [1, τ]]` is never positive semidefinite. (The proof, p. 1039,
treats `T₂ = 0` or `T₃ = 0` as "obvious"; only `T₂ = 0 ≠ T₃` fails.)
If `det(I − T₄Δ) ≠ 0` and `T(Δ) ⪰ 0` for every `Δ ∈ ℝ^{k×l}` with `‖Δ‖ ≤ 1`, then `‖T₄‖ < 1`
and some `τ ≥ 0` makes the block matrix (10) positive semidefinite. -/
theorem lemma22_necessity {d k l : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ) (hT₁ : T₁ = T₁ᵀ)
    (T₂ : Matrix (Fin d) (Fin k) ℝ) (T₃ : Matrix (Fin l) (Fin d) ℝ)
    (T₄ : Matrix (Fin l) (Fin k) ℝ) (hT : T₂ ≠ 0 ∨ T₃ = 0)
    (h9 : ∀ Δ : Matrix (Fin k) (Fin l) ℝ, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosSemidef) :
    specNorm T₄ < 1 ∧ ∃ τ : ℝ, 0 ≤ τ ∧ (lemma22Block T₁ T₂ T₃ T₄ τ).PosSemidef := by sorry

end RobustLS.LinFrac
