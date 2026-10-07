import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology

namespace KingmanSubadditive.PositiveMatrices

/-- Proof of Theorem 5, p. 892 (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973)), unnumbered: if `λ` is the almost-sure limit of `n⁻¹ log [X_n]₁₁`, then
for every `(i, j)`, `P{lim sup n⁻¹ log [X_n]_ij ≤ λ} = 1` (deduced in the paper from the same
bound for `X_n′ = Y₂ ⋯ Y_{n+1}` and stationarity).

**Formalization Note.** `λ` is any real random variable with `n⁻¹ log [X_n]₁₁ → λ` almost
surely. "lim sup aₙ ≤ λ" in the extended reals is encoded as: for every `ε > 0`, eventually
`aₙ ≤ λ + ε`. No shift-invariance of `λ` is assumed. -/
theorem limsup_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y)
    (lam : Ω → ℝ)
    (hlam : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Real.log (X Y n ω 0 0) / n) atTop (𝓝 (lam ω)))
    (i j : Fin k) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, Real.log (X Y n ω i j) / n ≤ lam ω + ε := by sorry

end KingmanSubadditive.PositiveMatrices

