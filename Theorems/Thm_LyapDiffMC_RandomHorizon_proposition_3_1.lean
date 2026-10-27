import Mathlib
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

/-- Proposition 3.1 (p. 11). For a non-negative kernel `Q`, a non-negative `f` and a
finite-valued non-negative `v` with `Qv ≤ v - f` (3.15), `Σₙ Qⁿ f ≤ v` (3.16). The measurable
space `S` plays the role of the paper's `C`; (3.15) is written additively, `Qv + f ≤ v`, which is
equivalent because `v` is finite. -/
theorem proposition_3_1 {S : Type*} [MeasurableSpace S] (Q : Kernel S S)
    (f v : S → ℝ≥0∞) (hf : Measurable f) (hv : Measurable v) (hv_fin : ∀ x, v x ≠ ⊤)
    (h315 : ∀ x, ∫⁻ y, v y ∂(Q x) + f x ≤ v x) :
    ∀ x, ∑' n, ∫⁻ y, f y ∂(Qpow Q n x) ≤ v x := by sorry

end LyapDiffMC.RandomHorizon

