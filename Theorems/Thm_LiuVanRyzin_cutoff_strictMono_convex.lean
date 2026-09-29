import Mathlib
import Definitions.Def_LiuVanRyzin_Model

namespace LiuVanRyzin

/-- Proposition 2 (Liu–van Ryzin 2008, p. 1120). The threshold `v(q)` is strictly increasing in
`q ∈ [0, 1)`; it is moreover convex in `q` if the utility has a nonnegative third derivative. -/
theorem cutoff_strictMono_convex (u : ℝ → ℝ) (hu : IsCustomerUtility u) (p₁ p₂ : ℝ)
    (hp : p₂ < p₁) :
    StrictMonoOn (fun q => cutoff u p₁ p₂ q) (Set.Ico 0 1) ∧
      (ContDiffOn ℝ 3 u (Set.Ioi 0) → (∀ x : ℝ, 0 < x → 0 ≤ iteratedDeriv 3 u x) →
        ConvexOn ℝ (Set.Ico 0 1) (fun q => cutoff u p₁ p₂ q)) := by sorry

end LiuVanRyzin
