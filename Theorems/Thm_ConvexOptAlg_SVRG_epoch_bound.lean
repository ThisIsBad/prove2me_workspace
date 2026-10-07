import Mathlib
import Definitions.Def_ConvexOptAlg_SVRG_Defs
import Definitions.Def_OnlineConvexOpt_ConvexBasics_StronglyConvexOn

open scoped InnerProductSpace

namespace ConvexOptAlg.SVRG

/-- The rearranged one-epoch inequality on p. 338, before substituting
`η = 1/(10β)` and `k = 20β/α`. The expectation is over all `k` samples. -/
theorem epoch_bound {n m : ℕ}
    (fs : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gs : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β η : ℝ) (k : ℕ) (y xstar : EuclideanSpace ℝ (Fin n))
    (hm : 0 < m) (hk : 0 < k) (hα : 0 < α) (hβ : 0 < β)
    (hη : 0 < η) (hηsmall : 2 * β * η < 1)
    (hfamily : SmoothConvexFamily fs gs β)
    (hstrong : OnlineConvexOpt.ConvexBasics.StronglyConvexOn
      Set.univ (objective fs) (fullGradient gs) α)
    (hmin : ∀ z, objective fs xstar ≤ objective fs z) :
    uniformMean (fun idx : Fin k → Fin m => objective fs (epochOut gs η k y idx)) -
        objective fs xstar ≤
      (1 / (α * η * (1 - 2 * β * η) * (k : ℝ)) +
        2 * β * η / (1 - 2 * β * η)) *
        (objective fs y - objective fs xstar) := by sorry

end ConvexOptAlg.SVRG

