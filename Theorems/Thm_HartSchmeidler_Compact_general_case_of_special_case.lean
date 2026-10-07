import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, p. 25, the general case: if a probability measure `p` on `S` satisfies
(4) for player `i` and every special-case deviation (`tⁱ` on a Borel set `Rⁱ`, the identity
elsewhere), then it satisfies (4) for player `i` and every Borel-measurable `ζⁱ : Sⁱ → Sⁱ`. -/
theorem general_case_of_special_case {ι : Type*} [Nonempty ι] [DecidableEq ι] {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, Nonempty (S i)] [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (h : ι → Profile S → ℝ) (hcont : ∀ i, Continuous (h i))
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (i : ι)
    (hspec : ∀ (t : S i) (R : Set (S i)), MeasurableSet R →
      Integrable
          (fun s : Profile S => h i s - h i (Function.update s i (specialDeviation t R (s i)))) p ∧
        0 ≤ ∫ s : Profile S,
          (h i s - h i (Function.update s i (specialDeviation t R (s i)))) ∂p)
    (ζ : S i → S i) (hζ : Measurable ζ) :
    Integrable (fun s : Profile S => h i s - h i (Function.update s i (ζ (s i)))) p ∧
      0 ≤ ∫ s : Profile S, (h i s - h i (Function.update s i (ζ (s i)))) ∂p := by sorry

end HartSchmeidler.Compact

