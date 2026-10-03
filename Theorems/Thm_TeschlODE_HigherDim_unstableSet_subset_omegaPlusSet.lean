import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_omegaPlusSet
import Definitions.Def_TeschlODE_HigherDim_stableSet
import Definitions.Def_TeschlODE_HigherDim_IsTrappingRegion

namespace TeschlODE.HigherDim

/-- Teschl, Lemma 8.6, p. 232, (8.11): for a trapping region `E`, the unstable set
`W⁻(x) = W⁻({x})` of every point `x ∈ ω₊(E)` is contained in `ω₊(E)`. -/
theorem unstableSet_subset_omegaPlusSet {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsTrappingRegion M I Φ E) :
    ∀ x ∈ omegaPlusSet M I Φ E, stableSet M I Φ (-1) {x} ⊆ omegaPlusSet M I Φ E := by sorry

end TeschlODE.HigherDim

