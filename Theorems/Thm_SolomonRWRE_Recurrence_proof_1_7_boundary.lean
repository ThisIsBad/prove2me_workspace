import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SolomonRWRE.Recurrence

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), §1, proof of
Theorem (1.7), p. 5, first paragraph: "If `α_n = 1`, (`α_n = 0`), with positive probability, but
`α_n > 0`, (`α_n < 1`), for all `n`, then it is clear that case (i), (case ii), holds."

**Formalization Note.** "Case (i) holds" is stated as both the hypothesis of Theorem (1.7)(i),
`Σ n⁻¹ P(ρ_n > 1) < ∞`, and its conclusion `X_n → ∞` a.e.; symmetrically for case (ii).
"With positive probability" is stated for `α_0` (the `α_n` are identically distributed), and
"for all `n`" for every outcome. The nondegeneracy hypothesis is inherited from
Theorem (1.7). -/
theorem proof_1_7_boundary {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (α : ℤ → Ω → ℝ) (X : ℕ → Ω → ℤ) (hRW : IsRWRE P α X)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ ω ∂P, α 0 ω = c) :
    ((0 < P {ω | α 0 ω = 1} ∧ ∀ n ω, 0 < α n ω) →
        seriesGt P α ≠ ∞ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    ((0 < P {ω | α 0 ω = 0} ∧ ∀ n ω, α n ω < 1) →
        seriesLt P α ≠ ∞ ∧ ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) := by sorry

end SolomonRWRE.Recurrence

