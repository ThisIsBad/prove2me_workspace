import Mathlib
import Definitions.Def_LassoDantzig_Equivalence_Model

namespace LassoDantzig.Equivalence

/-- (B.17), deterministic form: on the event `𝒜`, under RE(s, 1) with witness `κ`, for every
Lasso solution `β̂_L` with `𝓜(β̂_L) ≤ s` and every Dantzig selector `β̂_D`,
`‖f̂_L − f‖_n² ≤ ‖f̂_D − f‖_n² + 9 f_max² r² 𝓜(β̂_L) / κ²`. -/
theorem eq_B17_lasso_side {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (X : Matrix (Fin n) (Fin M) ℝ) (f w : Fin n → ℝ) (hX : ∀ j, colNorm X j ≠ 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hsM : s ≤ M) (κ : ℝ) (hκ : 0 < κ) (hRE : RE X s 1 κ)
    (r : ℝ) (hr : 0 < r) (hw : NoiseEventHalf X r w)
    (βL βD : Fin M → ℝ) (hL : IsLasso X (fun i => f i + w i) r βL)
    (hD : IsDantzig X (fun i => f i + w i) r βD) (hsp : sparsity βL ≤ s) :
    predLoss X f βL ≤
      predLoss X f βD + 9 * fmax X ^ 2 * r ^ 2 * (sparsity βL : ℝ) / κ ^ 2 := by sorry

end LassoDantzig.Equivalence
