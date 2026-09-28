import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian
open Filter Topology

namespace NonsmoothNewton.AugLagrangian

/-- Qi–Sun (1993), Section 4, Eq. (4.7), p. 364. Let `r > 0`, `g ∈ C²`, and let `(x̄, s̄)` lie on
the surface `s̄ + r g(x̄) = 0` (4.3). If `h_j → h`, `α_j → α`, `t_j ↓ 0` and
`s̄ + t_j α_j + r g(x̄ + t_j h_j) = 0` for every `j` (4.6), then `α + r ∇g(x̄)ᵀ h = 0`. -/
theorem tangency_4_7 {n : ℕ} (r : ℝ) (hr : 0 < r) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ 2 g) (xbar : EuclideanSpace ℝ (Fin n)) (sbar : ℝ)
    (h43 : sbar + r * g xbar = 0)
    (h : EuclideanSpace ℝ (Fin n)) (α : ℝ)
    (hj : ℕ → EuclideanSpace ℝ (Fin n)) (αj tj : ℕ → ℝ)
    (hhj : Tendsto hj atTop (𝓝 h)) (hαj : Tendsto αj atTop (𝓝 α))
    (htj : Tendsto tj atTop (𝓝[>] 0))
    (h46 : ∀ j, sbar + tj j * αj j + r * g (xbar + tj j • hj j) = 0) :
    α + r * fderiv ℝ g xbar h = 0 := by sorry

end NonsmoothNewton.AugLagrangian
