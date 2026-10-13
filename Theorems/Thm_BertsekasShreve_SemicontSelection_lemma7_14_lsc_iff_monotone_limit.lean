import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Lemma 7.14 (Bertsekas & Shreve, p. 147). Let `X` be metrizable and `f : X → R*`.
(a) `f` is lower semicontinuous and bounded below (by a real number) iff there is a sequence
`f_n` of bounded continuous real functions with `f_n ↑ f` pointwise.
(b) `f` is upper semicontinuous and bounded above iff there is such a sequence with `f_n ↓ f`. -/
theorem lemma7_14_lsc_iff_monotone_limit {X : Type*} [TopologicalSpace X] [MetrizableSpace X]
    (f : X → EReal) :
    ((LowerSemicontinuous f ∧ ∃ b : ℝ, ∀ x, (b : EReal) ≤ f x) ↔
      ∃ g : ℕ → (BoundedContinuousFunction X ℝ), (∀ n x, g n x ≤ g (n + 1) x) ∧
        ∀ x, Filter.Tendsto (fun n => ((g n x : ℝ) : EReal)) Filter.atTop (nhds (f x))) ∧
    ((UpperSemicontinuous f ∧ ∃ b : ℝ, ∀ x, f x ≤ (b : EReal)) ↔
      ∃ g : ℕ → (BoundedContinuousFunction X ℝ), (∀ n x, g (n + 1) x ≤ g n x) ∧
        ∀ x, Filter.Tendsto (fun n => ((g n x : ℝ) : EReal)) Filter.atTop (nhds (f x))) := by sorry

end BertsekasShreve.SemicontSelection

