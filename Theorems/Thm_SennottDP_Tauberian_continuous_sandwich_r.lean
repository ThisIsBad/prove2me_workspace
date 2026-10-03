import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_KaramataR

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- Sennott (1999), p. 280, Lemma A.4.1: given `ε > 0` there are continuous functions `s` and `s*`
with `s* ≤ r ≤ s` on `(0, 1)` and (A.27) `1 − ε ≤ ∫_0^1 s* ≤ ∫_0^1 s ≤ 1 + ε`.
Continuity is required on the closed interval `[0, 1]` (the functions of Figs. A.2–A.3 are), which
is what the Weierstrass step of the proof of Theorem A.4.2 uses. -/
theorem continuous_sandwich_r (ε : ℝ) (hε : 0 < ε) :
    ∃ s sstar : ℝ → ℝ, ContinuousOn s (Set.Icc 0 1) ∧ ContinuousOn sstar (Set.Icc 0 1) ∧
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, sstar x ≤ r x ∧ r x ≤ s x) ∧
      1 - ε ≤ ∫ x in (0 : ℝ)..1, sstar x ∧
      ∫ x in (0 : ℝ)..1, sstar x ≤ ∫ x in (0 : ℝ)..1, s x ∧
      ∫ x in (0 : ℝ)..1, s x ≤ 1 + ε := by sorry

end SennottDP.Tauberian
