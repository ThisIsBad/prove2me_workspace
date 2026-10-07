import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting

namespace MassartDKW.Binom

/-- Massart (1990), Lemma 1(i), p. 1272: `φ` is a positive (for `t > 0`; `φ(0) = 0`), increasing,
convex function on `[0, ∞)` with `φ(t)/t → 1/4` as `t → ∞`. -/
theorem lemma_1_i :
    (∀ t : ℝ, 0 < t → 0 < phi t) ∧
    StrictMonoOn phi (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) phi ∧
    Filter.Tendsto (fun t => phi t / t) Filter.atTop (nhds (1 / 4)) := by sorry

end MassartDKW.Binom

