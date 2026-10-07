import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology

namespace KingmanSubadditive.PositiveMatrices

/-- Proof of Theorem 5, p. 891 (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973)), unnumbered: under the hypotheses of Theorem 5, `x_st = −log z_st` with
`z_st = [Y_{s+1} ⋯ Y_t]₁₁` satisfies S₁; since `(Y_n)` is stationary, S₂ holds; and each
`x_st` (`s < t`) is a random variable with finite expectation `g_{t−s}`.

**Formalization Note.** S₁ is pointwise (every outcome), S₂ is equality of the joint laws of
the two-parameter paths `(x_{s+1,t+1})` and `(x_st)` over pairs `s < t`. "Finite expectation
`g_{t−s}`" is integrability of `x_st` together with `E(x_st) = E(x_{0,t−s})`. -/
theorem x_subadditive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    (∀ s t : ℕ, s < t → Measurable (x Y s t)) ∧ KingmanSubadditive.Ergodic.S1 (x Y) ∧ KingmanSubadditive.Ergodic.S2 P (x Y) ∧
    (∀ s t : ℕ, s < t → Integrable (x Y s t) P ∧ ∫ ω, x Y s t ω ∂P = g P (x Y) (t - s)) := by sorry

end KingmanSubadditive.PositiveMatrices

