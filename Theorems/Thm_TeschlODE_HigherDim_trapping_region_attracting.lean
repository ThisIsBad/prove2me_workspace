import Mathlib
import Definitions.Def_TeschlODE_HigherDim_IsIntegralCurve
import Definitions.Def_TeschlODE_HigherDim_IsMaximalFlow
import Definitions.Def_TeschlODE_HigherDim_omegaPlusSet
import Definitions.Def_TeschlODE_HigherDim_stableSet
import Definitions.Def_TeschlODE_HigherDim_IsInvariant
import Definitions.Def_TeschlODE_HigherDim_IsAttracting
import Definitions.Def_TeschlODE_HigherDim_IsTrappingRegion

namespace TeschlODE.HigherDim

/-- Teschl, Lemma 8.5, p. 232, (8.10): for a trapping region `E` of the flow of a `C¹` vector
field on the open set `M ⊆ ℝⁿ`, `Λ = ω₊(E) = ⋂_{t ≥ 0} Φ(t, E)` is a nonempty, invariant,
compact, and connected attracting set. -/
theorem trapping_region_attracting {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsTrappingRegion M I Φ E) :
    omegaPlusSet M I Φ E = (⋂ t : ℝ, ⋂ (_ : 0 ≤ t), Φ t '' E) ∧
      (omegaPlusSet M I Φ E).Nonempty ∧ IsInvariant M I Φ (omegaPlusSet M I Φ E) ∧
      IsCompact (omegaPlusSet M I Φ E) ∧ IsConnected (omegaPlusSet M I Φ E) ∧
      IsAttracting M I Φ (omegaPlusSet M I Φ E) := by sorry

end TeschlODE.HigherDim

