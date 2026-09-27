import Mathlib
import Definitions.Def_OnlineConvexOpt_Introduction_Hedge

namespace OnlineConvexOpt.Introduction

/-- **Theorem 1.5** (Hedge's loss bound), Hazan, *Introduction to Online Convex
Optimization*, 2nd ed., arXiv:1909.05207v3, p. 12.

"Let `ℓ²_t` denote the `N`-dimensional vector of square losses, i.e., `ℓ²_t(i) = ℓ_t(i)²`,
let `ε > 0`, and assume all losses to be non-negative. The Hedge algorithm satisfies for any
expert `i⋆ ∈ [N]`: `∑_{t=1}^T x_t^⊤ ℓ_t ≤ ∑_{t=1}^T ℓ_t(i⋆) + ε ∑_{t=1}^T x_t^⊤ ℓ²_t + log N / ε`." -/
theorem hedge_loss_bound {N : ℕ} (hN : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (ℓ x W : ℕ → Fin N → ℝ) (hnonneg : ∀ t i, 0 ≤ ℓ t i)
    (hrun : IsHedgeRun ε ℓ W x) (T : ℕ) (istar : Fin N) :
    expectedLoss x ℓ T ≤
      expertLoss ℓ istar T + ε * expectedLoss x (fun t i => ℓ t i ^ 2) T + Real.log N / ε := by sorry

end OnlineConvexOpt.Introduction
