import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology

namespace KingmanSubadditive.PositiveMatrices

/-- Proof of Theorem 5, (2.2.3), p. 892 (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973)): if `λ` is the almost-sure limit of `n⁻¹ log [X_n]₁₁`, then for every
`(i, j)`, `P{lim inf n⁻¹ log [X_n]_ij ≥ λ} = 1`.

**Formalization Note.** `λ` is any real random variable with `n⁻¹ log [X_n]₁₁ → λ` almost
surely (the limit of the preceding milestone). "lim inf aₙ ≥ λ" in the extended reals is
encoded without a real `liminf` (whose junk value on unbounded sequences would change the
claim) as: for every `ε > 0`, eventually `aₙ ≥ λ − ε`. -/
theorem liminf_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y)
    (lam : Ω → ℝ)
    (hlam : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Real.log (X Y n ω 0 0) / n) atTop (𝓝 (lam ω)))
    (i j : Fin k) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, lam ω - ε ≤ Real.log (X Y n ω i j) / n := by sorry

end KingmanSubadditive.PositiveMatrices

