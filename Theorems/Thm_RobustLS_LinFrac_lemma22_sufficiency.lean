import Mathlib
import Definitions.Def_RobustLS_LinFrac_Core

open Matrix

namespace RobustLS.LinFrac

/-- El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data,
SIAM J. Matrix Anal. Appl. 18(4) (1997), §2.2, Lemma 2.2, "if" direction, p. 1038 (PDF p. 4).
Let `T₁ = T₁ᵀ ∈ ℝ^{d×d}`, `T₂ ∈ ℝ^{d×k}`, `T₃ ∈ ℝ^{l×d}`, `T₄ ∈ ℝ^{l×k}`. If `‖T₄‖ < 1` and
there is `τ ≥ 0` with the block matrix (10) positive semidefinite, then for every
`Δ ∈ ℝ^{k×l}` with `‖Δ‖ ≤ 1` (largest singular value) we have `det(I − T₄Δ) ≠ 0` and
`T(Δ) ⪰ 0` (Eq. (9)). -/
theorem lemma22_sufficiency {d k l : ℕ} (T₁ : Matrix (Fin d) (Fin d) ℝ) (hT₁ : T₁ = T₁ᵀ)
    (T₂ : Matrix (Fin d) (Fin k) ℝ) (T₃ : Matrix (Fin l) (Fin d) ℝ)
    (T₄ : Matrix (Fin l) (Fin k) ℝ) (hT₄ : specNorm T₄ < 1) (τ : ℝ) (hτ : 0 ≤ τ)
    (h10 : (lemma22Block T₁ T₂ T₃ T₄ τ).PosSemidef) :
    ∀ Δ : Matrix (Fin k) (Fin l) ℝ, specNorm Δ ≤ 1 →
      (1 - T₄ * Δ).det ≠ 0 ∧ (lftT T₁ T₂ T₃ T₄ Δ).PosSemidef := by sorry

end RobustLS.LinFrac
