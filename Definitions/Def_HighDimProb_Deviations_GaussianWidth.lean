import Mathlib
import Definitions.Def_HighDimProb_Deviations_ExpSup

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Deviations

/-- The **Gaussian width** `w(T)` of a subset `T ⊆ ℝⁿ`. Vershynin, *High-Dimensional Probability*
(2018), Definition 7.5.1, p. 173 (PDF p. 181): "The Gaussian width of a subset `T ⊂ ℝⁿ` is defined
as `w(T) := E sup_{x∈T} ⟨g,x⟩` where `g ∼ N(0, Iₙ)`." Same realization of `g ∼ N(0,Iₙ)` as
`gaussianComplexity` (Mathlib's `ProbabilityTheory.stdGaussian` on `EuclideanSpace ℝ (Fin n)`, via
its identity map); `E sup` is `expSup`. Unlike `gaussianComplexity`, no absolute value is taken
inside the supremum, matching the book's own distinction between the two "cousin" quantities
(Section 7.6.2: `w(T) ≤ γ(T)`, with equality when `T` is origin-symmetric). -/
noncomputable def gaussianWidth {n : ℕ} (T : Set (EuclideanSpace ℝ (Fin n))) : EReal :=
  expSup (stdGaussian (EuclideanSpace ℝ (Fin n))) (fun x : T => fun g => inner (𝕜 := ℝ) g x.1)

end HighDimProb.Deviations
