import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

/-- Lemma B.1, (B.2), on the event `𝒜`: if the noise `w` lies in `𝒜` (i.e. (B.5),
`|(1/n) D^{−1/2} Xᵀ w|_∞ ≤ r/2`) and `y = f + w`, every Lasso solution `β̂_L` satisfies
`|(1/n) Xᵀ(f − Xβ̂_L)|_∞ ≤ 3 r f_max / 2`. -/
theorem lemma_B1_eq_B2 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hw : NoiseEventHalf X r w) (βL : Fin M → ℝ) (hL : IsLasso X (fun i => f i + w i) r βL) :
    ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (f i - X.mulVec βL i)| ≤ 3 * r * fmax X / 2 := by sorry

end LassoDantzig.Equivalence
