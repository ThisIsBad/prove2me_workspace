import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Corollary 4.4**, p. 10: if `L_Ω(x_0)` is compact, `f` is `C¹` and
`liminf_{k→∞} ‖q(x_k)‖ ≠ 0` (encoded as: it is not the case that `‖q(x_k)‖ < ε` infinitely often
for every `ε > 0`), then there is `Δ_* > 0` with `Δ_k > Δ_*` for all `k`. -/
theorem corollary_4_4 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0)))
    (hliminf : ¬ ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ‖projQ lo hi f (R.x k)‖ < ε) :
    ∃ Δstar : ℝ, 0 < Δstar ∧ ∀ k, Δstar < R.Δ k := by sorry

end LewisTorczon.BoundPS
