import Mathlib
import Definitions.Def_DeterioratingJobs_Weighted_Model

namespace DeterioratingJobs.Weighted

/-- The unnumbered interchange display between (8) and Proposition 2, p. 497.
The printed multiplication dot preceding the second bracket is corrected to addition. -/
theorem interchange_identity {Ω : Type*} {N : ℕ}
    (X : Fin N → Ω → ℝ) (α c : Fin N → ℝ)
    (π : Equiv.Perm (Fin N)) (p : Fin N) (hp : p.val + 1 < N) (ω : Ω) :
    let q : Fin N := ⟨p.val + 1, hp⟩
    let a := π p
    let b := π q
    let π₁ := π * Equiv.swap p q
    totalCost X α c π ω - totalCost X α c π₁ ω =
      DeterioratingJobs.Makespan.completionTime X α π p.val ω *
        (c b * α a * (1 + α b) - c a * α b * (1 + α a)) +
      (X a ω * c b * (1 + α b) - X b ω * c a * (1 + α a)) +
      ∑ r : Fin N with p.val + 2 ≤ r.val,
        c (π r) *
          (∏ k : Fin N with p.val + 2 ≤ k.val ∧ k ≤ r, (1 + α (π k))) *
          (X a ω * α b - X b ω * α a) := by sorry

end DeterioratingJobs.Weighted

