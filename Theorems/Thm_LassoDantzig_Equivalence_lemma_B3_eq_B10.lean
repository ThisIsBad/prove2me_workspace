import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

/-- Lemma B.3, (B.10), on the event `ℬ`: if the noise `w` satisfies
`|(1/n) D^{−1/2} Xᵀ w|_∞ ≤ r` and `y = f + w`, every Dantzig selector `β̂_D` satisfies
`|(1/n) Xᵀ(f − Xβ̂_D)|_∞ ≤ 2 r f_max`. -/
theorem lemma_B3_eq_B10 {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hw : NoiseEvent X r w) (βD : Fin M → ℝ) (hD : IsDantzig X (fun i => f i + w i) r βD) :
    ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (f i - X.mulVec βD i)| ≤ 2 * r * fmax X := by sorry

end LassoDantzig.Equivalence
