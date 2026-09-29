import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Proposition 4.3**, first part, p. 9: if `L_Ω(x_0)` is compact and `f` is `C¹`, then for every
`η > 0` there is `δ > 0`, independent of `k`, such that `Δ_k < δ` and `‖q(x_k)‖ > η` imply that
the method finds an acceptable step: `f(x_k + s_k) < f(x_k)` and `x_k + s_k ∈ Ω`. -/
theorem proposition_4_3_first {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0))) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ k, R.Δ k < δ → η < ‖projQ lo hi f (R.x k)‖ →
      f (R.x k + R.s k) < f (R.x k) ∧ R.x k + R.s k ∈ box lo hi := by sorry

end LewisTorczon.BoundPS
