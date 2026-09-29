import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Proposition 4.2**, p. 8. If `q(x_k) ≠ 0`, there is `ν_k > 0` (depending on the iteration `k`
through `x_k` and `M_k`, but not on the step length) such that for every step length
`0 < Δ < ν_k` some column `c` of `Γ_k = [M_k  -M_k]` gives a trial step `s = Δ B c` with
`x_k + s ∈ Ω` and `g_kᵀ s ≤ -c_n ‖q_k‖ ‖s‖`, `c_n = n^{-1/2}`. -/
theorem proposition_4_2 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hΩU : box lo hi ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (R : GPSRun n m) (hR : IsGPSRun P lo hi f R) (k : ℕ)
    (hq : projQ lo hi f (R.x k) ≠ 0) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ Δ : ℝ, 0 < Δ → Δ < ν →
      ∃ c ∈ coreCols R k, R.x k + stepOf P Δ c ∈ box lo hi ∧
        inner ℝ (gradient f (R.x k)) (stepOf P Δ c) ≤
          -(1 / Real.sqrt n) * ‖projQ lo hi f (R.x k)‖ * ‖stepOf P Δ c‖ := by sorry

end LewisTorczon.BoundPS
