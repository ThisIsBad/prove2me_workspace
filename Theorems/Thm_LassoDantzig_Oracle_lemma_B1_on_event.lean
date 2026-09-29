import Mathlib
import Definitions.Def_LassoDantzig_Oracle_Model

open MeasureTheory ProbabilityTheory

namespace LassoDantzig.Oracle

/-- **Lemma B.1, (B.1), deterministic core** (p. 21, proof of Lemma B.1: "so that on 𝒜 we get
(B.1)"). Let `w = y − f` lie in the event `𝒜`, i.e. `2|n⁻¹ ∑ᵢ X_{ij} w_i| ≤ r ‖f_j‖_n` for every
`j`, and let `β̂` be any Lasso solution (2.1) with tuning constant `r > 0`. Then for every
`β ∈ ℝ^M`:
`‖f̂_L − f‖_n² + r ∑_j ‖f_j‖_n |β̂_j − β_j| ≤ ‖f_β − f‖_n² + 4r ∑_{j ∈ J(β)} ‖f_j‖_n |β̂_j − β_j|
  ≤ ‖f_β − f‖_n² + 4r √𝓜(β) √(∑_{j ∈ J(β)} ‖f_j‖_n² |β̂_j − β_j|²)`. -/
theorem lemma_B1_on_event {n M : ℕ} (hn : 1 ≤ n) (X : Matrix (Fin n) (Fin M) ℝ)
    (f y : Fin n → ℝ) (r : ℝ) (hr : 0 < r) (hA : NoiseBound X (fun i => y i - f i) r)
    (βhat : Fin M → ℝ) (hL : IsLasso X y r βhat) (β : Fin M → ℝ) :
    empSq (fun i => X.mulVec βhat i - f i) + r * ∑ j, colNorm X j * |βhat j - β j| ≤
        empSq (fun i => X.mulVec β i - f i) +
          4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ∧
      empSq (fun i => X.mulVec β i - f i) +
          4 * r * ∑ j ∈ supp β, colNorm X j * |βhat j - β j| ≤
        empSq (fun i => X.mulVec β i - f i) +
          4 * r * Real.sqrt (sparsity β) *
            Real.sqrt (∑ j ∈ supp β, colNorm X j ^ 2 * |βhat j - β j| ^ 2) := by sorry

end LassoDantzig.Oracle
