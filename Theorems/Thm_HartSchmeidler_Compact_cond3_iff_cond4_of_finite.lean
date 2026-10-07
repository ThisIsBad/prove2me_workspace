import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- p. 23: when the strategy set `Sⁱ` of player `i` is finite, condition (3) for player `i`
(one inequality per recommendation `r` and deviation `t`) is equivalent to condition (4) for
player `i` (one inequality per measurable deviation map `ζ : Sⁱ → Sⁱ`). -/
theorem cond3_iff_cond4_of_finite {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    [∀ j, TopologicalSpace (S j)] [∀ j, MeasurableSpace (S j)] [∀ j, BorelSpace (S j)]
    (h : ι → Profile S → ℝ) (i : ι) [Fintype (S i)] [DiscreteTopology (S i)]
    (hmeas : Measurable (h i)) (hbdd : ∃ M : ℝ, ∀ s, |h i s| ≤ M)
    (p : Measure (Profile S)) [IsProbabilityMeasure p] :
    (∀ r t : S i,
        0 ≤ ∫ s in {s : Profile S | s i = r}, (h i s - h i (Function.update s i t)) ∂p) ↔
      (∀ ζ : S i → S i, Measurable ζ →
        0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (ζ (s i)))) ∂p) := by sorry

end HartSchmeidler.Compact

