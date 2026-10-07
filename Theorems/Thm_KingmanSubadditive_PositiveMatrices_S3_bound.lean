import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology

namespace KingmanSubadditive.PositiveMatrices

/-- Proof of Theorem 5, p. 892 (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973)), unnumbered: with `‖A‖ = max_i Σ_j |[A]_ij|` the ℓ₁-norm,
`E{log ‖Y₁‖} < ∞` and `inf g_n/n ≥ −E{log ‖Y₁‖} > −∞`, so S₃ is satisfied by
`x_st = −log [Y_{s+1} ⋯ Y_t]₁₁`.

**Formalization Note.** "`E{log ‖Y₁‖}` is finite" is integrability of `log ‖Y₁‖`
(`‖Y₁‖ > 0` under positivity, so the logarithm is the genuine one). The infimum over `n ≥ 1` is
written as the bound `g_n ≥ −n·E{log ‖Y₁‖}` for every `n ≥ 1`, which is equivalent and avoids
Lean's junk value for an unbounded real infimum. -/
theorem S3_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    Integrable (fun ω => Real.log (rowSumNorm (Y 1 ω))) P ∧
    ∀ n : ℕ, 1 ≤ n →
      -((n : ℝ) * ∫ ω, Real.log (rowSumNorm (Y 1 ω)) ∂P) ≤ g P (x Y) n := by sorry

end KingmanSubadditive.PositiveMatrices

